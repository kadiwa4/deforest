use proc_macro2::{Literal, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{Attribute, Expr, GenericParam, ItemStruct, Lit, Meta};

#[derive(Clone, Copy)]
enum ItemKind {
	Property,
	Child,
	Children,
}

/// Derive macro generating an impl of the trait `DeserializeNode`.
///
/// Requires an implementation of `Default`.
///
/// Attribute syntax: `#[dt_*]` or `#[dt_* = "<item name>"]`
///
/// The default item name is the field name with undescores replaced by hyphens
/// (and a `#` prepended in case the name ends with `_cells`).
/// The unit-address is ignored.
///
/// - `#[dt_property]` (default) uses `DeserializeProperty`
/// - `#[dt_child]` uses `DeserializeNode`
/// - `#[dt_children]` uses `ExtendDeserializedNode` to collect items of type
///   `Self::Node`; it is equivalent to `Extend<Self::Node>`
///
/// `DeserializeNode::deserialize` is always used with an appropriate
/// `NodeContext`.
#[proc_macro_derive(DeserializeNode, attributes(dt_property, dt_child, dt_children))]
pub fn derive_deserialize_node(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let strct: ItemStruct = syn::parse(tokens).expect("invalid struct");

	let update_address_cells_stmts = quote! {
		let ::devicetree::prop_value::AddressCells(address_cells) = ::devicetree::DeserializeProperty::deserialize(prop, cx)?;
		child_cx.address_cells = address_cells;
	};
	let update_size_cells_stmts = quote! {
		let ::devicetree::prop_value::SizeCells(size_cells) = ::devicetree::DeserializeProperty::deserialize(prop, cx)?;
		child_cx.size_cells = size_cells;
	};

	let (mut prop_match_arms, mut child_match_arms) = (TokenStream::new(), TokenStream::new());
	let (mut have_address_cells, mut have_size_cells) = (false, false);
	for (idx, field) in strct.fields.into_iter().enumerate() {
		let attr_info = parse_field_attrs(&field.attrs, || match field.ident {
			None => idx.to_string(),
			Some(ref i) => i.to_string(),
		});
		let (kind, item_name) = attr_info.unwrap_or((ItemKind::Property, None));
		let item_name = item_name.unwrap_or_else(|| {
			let name = field
				.ident
				.as_ref()
				.unwrap_or_else(|| panic!("field {idx} needs an explicit name"))
				.to_string();
			let start_hash = if name.ends_with("_cells") { "#" } else { "" };
			format!("{start_hash}{}", name.replace('_', "-"))
		});
		let field_name = match field.ident {
			None => TokenTree::Literal(Literal::usize_unsuffixed(idx)),
			Some(i) => TokenTree::Ident(i),
		};
		let ty = field.ty;
		match kind {
			ItemKind::Property => {
				let update_cx = match &item_name[..] {
					"#address-cells" => {
						have_address_cells = true;
						Some(&update_address_cells_stmts)
					}
					"#size-cells" => {
						have_size_cells = true;
						Some(&update_size_cells_stmts)
					}
					_ => None,
				};
				prop_match_arms.extend(quote! {
					#item_name => {
						this.#field_name = <#ty as ::devicetree::DeserializeProperty<'dtb>>::deserialize(prop, cx)?;
						#update_cx
					}
				});
			},
			ItemKind::Child => child_match_arms.extend(quote! {
				#item_name => (this.#field_name, cursor) = <#ty as ::devicetree::DeserializeNode<'dtb>>::deserialize(&node, &child_cx)?,
			}),
			ItemKind::Children => child_match_arms.extend(quote! {
				#item_name => {
					let val;
					(val, cursor) = ::devicetree::DeserializeNode::deserialize(&node, &child_cx)?;
					<#ty as ::devicetree::ExtendDeserializedNode>::_extend_(&mut this.#field_name, ::core::iter::once(val));
				}
			}),
		};
	}
	if !have_address_cells {
		prop_match_arms.extend(quote! {
			"#address-cells" => { #update_address_cells_stmts }
		});
	}
	if !have_size_cells {
		prop_match_arms.extend(quote! {
			"#size-cells" => { #update_size_cells_stmts }
		});
	}

	let name = strct.ident;
	let (impl_generics, ty_generics, where_clause) = strct.generics.split_for_impl();
	let mut impl_generics = impl_generics.into_token_stream();
	if !strct
		.generics
		.params
		.iter()
		.any(|p| matches!(p, GenericParam::Lifetime(def) if def.lifetime.ident == "dtb"))
	{
		let mut other = impl_generics.into_iter();
		if let Some(lt_token) = other.next() {
			impl_generics = quote! { #lt_token 'dtb, };
			impl_generics.extend(other);
		} else {
			impl_generics = quote! { <'dtb> };
		}
	}
	let child_arm = if child_match_arms.is_empty() {
		quote! {
			::devicetree::blob::Item::Child(_) => {
				return ::devicetree::Result::Ok((this, items.end_cursor()?))
			}
		}
	} else {
		quote! {
			::devicetree::blob::Item::Child(node) => {
				let cursor;
				match node.split_name()?.0 {
					#child_match_arms
					_ => continue,
				}
				items = ::devicetree::blob::NodeItems::new(blob_node, cursor);
			}
		}
	};
	quote! {
		impl #impl_generics ::devicetree::DeserializeNode<'dtb> for #name #ty_generics #where_clause {
			fn deserialize(
				blob_node: &::devicetree::blob::Node<'dtb>,
				cx: &::devicetree::NodeContext,
			) -> ::devicetree::Result<(Self, ::devicetree::blob::Cursor)> {
				let mut this: Self = ::core::default::Default::default();
				let mut items = blob_node.items();
				let mut child_cx: ::devicetree::NodeContext = ::core::default::Default::default();
				while let ::core::option::Option::Some(item) =
					::devicetree::fallible_iterator::FallibleIterator::next(&mut items)?
				{
					match item {
						::devicetree::blob::Item::Property(prop) => match prop.name()? {
							#prop_match_arms
							_ => (),
						},
						#child_arm
					}
				}
				::devicetree::Result::Ok((this, items._cursor_()))
			}
		}
	}
	.into()
}

fn parse_field_attrs(
	attrs: &[Attribute],
	mut field_name: impl FnMut() -> String,
) -> Option<(ItemKind, Option<String>)> {
	let mut relevant_attrs = attrs.iter().filter_map(|attr| {
		let mut panic_invalid = |attr_name| -> ! {
			panic!(
				"invalid attribute on field `{}`: `{}`
Valid forms are:
- `#[{attr_name}]`
- `#[{attr_name} = \"<item name>\"]`",
				field_name(),
				attr.to_token_stream(),
			)
		};

		let (path, value_lit) = match &attr.meta {
			Meta::Path(path) => (path, None),
			// error later if the attribute was actually intended for this macro
			Meta::List(list) => (&list.path, None),
			Meta::NameValue(name_value) => {
				let Expr::Lit(ref value_lit) = name_value.value else {
					panic_invalid(name_value.path.get_ident()?.to_string())
				};
				(&name_value.path, Some(&value_lit.lit))
			}
		};
		let attr_name = path.get_ident()?.to_string();
		let kind = match &*attr_name {
			"dt_property" => ItemKind::Property,
			"dt_child" => ItemKind::Child,
			"dt_children" => ItemKind::Children,
			_ => return None,
		};

		if let Meta::List(_) = attr.meta {
			panic_invalid(attr_name);
		}
		let item_name = match value_lit {
			None => None,
			Some(Lit::Str(name)) => {
				let name = name.value();
				assert!(
					!name.contains('@'),
					"item name of field `{}` contains unit-address",
					field_name()
				);
				Some(name)
			}
			Some(_) => panic_invalid(attr_name),
		};
		Some((kind, item_name))
	});
	let ret = relevant_attrs.next()?;
	if relevant_attrs.next().is_some() {
		panic!("duplicate attributes on field `{}`", field_name());
	}
	Some(ret)
}
