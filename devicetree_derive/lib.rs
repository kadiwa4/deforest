#![warn(rust_2018_idioms)]
#![warn(macro_use_extern_crate, meta_variable_misuse, missing_abi)]
#![warn(unused_lifetimes, unused_macro_rules, unused_qualifications)]

use proc_macro2::{Literal, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{Attribute, Expr, GenericParam, ItemStruct, Lit, Meta};

#[derive(Clone, Copy)]
enum ItemKind {
	SelfStartCursor,
	SelfName,
	SelfUnitAddress,
	Property,
	Child,
	Children,
	ChildrenRest,
}

/// Derive macro generating an impl of the trait `DeserializeNode`.
///
/// Requires an implementation of `Default`.
///
/// Attribute syntax (except for `dt_self`):
/// For the other attributes:
/// - `#[dt_*]`
/// - `#[dt_* = "<item name>"]`
/// - `#[dt_children(rest)]`
///
/// The default item name is the field name with undescores replaced by hyphens
/// (and a `#` prepended in case the name ends with `_cells`), except
/// `device_type`, which uses an underscore.
/// The unit address is ignored.
///
/// - `#[dt_self(start_cursor)]` stores a cursor to the containing node in that
///   field (type `Option<Cursor>`).
/// - `#[dt_self(name)]` stores the containing node's entire name in that field
///   (type `T where T: From<&'dtb str>`).
/// - `#[dt_self(unit_address)]` stores the containing node's unit address in
///   that field (type `Option<T> where T: From<&'dtb str>`).
///
/// - `#[dt_property]` (default) uses `DeserializeProperty`
/// - `#[dt_child]` uses `DeserializeNode`
/// - `#[dt_children]` uses `PushDeserializedNode` to collect items of type
///   `Self::Node`; it is similar to `Extend<Self::Node>`
///
/// `DeserializeNode::deserialize` is always used with an appropriate
/// `NodeContext`.
///
/// The lifetime `'dtb` (if it exists) is special because it will be used for
/// the `DeserializeNode<'dtb>` implementation.
#[proc_macro_derive(
	DeserializeNode,
	attributes(dt_self, dt_property, dt_child, dt_children)
)]
pub fn derive_deserialize_node(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let strct: ItemStruct = syn::parse(tokens).expect("invalid struct");

	let (mut start_cursor_fields, mut name_fields, mut unit_address_fields) =
		(Vec::new(), Vec::new(), Vec::new());
	let mut prop_match_arms = TokenStream::new();
	let (mut child_match_arms, mut children_rest_stmts) = (TokenStream::new(), None);
	for (idx, field) in strct.fields.into_iter().enumerate() {
		let attr_info = parse_field_attrs(&field.attrs, || match field.ident {
			None => idx.to_string(),
			Some(ref i) => i.to_string(),
		});
		let (kind, item_name) = attr_info.unwrap_or((ItemKind::Property, None));
		let field_name = match field.ident {
			None => TokenTree::Literal(Literal::usize_unsuffixed(idx)),
			Some(ref i) => TokenTree::Ident(i.clone()),
		};
		match kind {
			ItemKind::SelfStartCursor => {
				start_cursor_fields.push(field_name);
				continue;
			}
			ItemKind::SelfName => {
				name_fields.push(field_name);
				continue;
			}
			ItemKind::SelfUnitAddress => {
				unit_address_fields.push(field_name);
				continue;
			}
			_ => (),
		}
		let item_name = item_name.unwrap_or_else(|| {
			let ident = field
				.ident
				.as_ref()
				.unwrap_or_else(|| panic!("field {idx} needs an explicit name"));
			field_to_node_name(ident.to_string())
		});
		let ty = field.ty;
		match kind {
			ItemKind::SelfStartCursor | ItemKind::SelfName | ItemKind::SelfUnitAddress => unreachable!(),
			ItemKind::Property => {
				prop_match_arms.extend(quote! {
					#item_name => {
						this.#field_name = <#ty as ::devicetree::DeserializeProperty<'dtb>>::deserialize(prop, cx)?
					}
				});
			},
			ItemKind::Child => child_match_arms.extend(quote! {
				#item_name => {
					(this.#field_name, *cursor) = <#ty as ::devicetree::DeserializeNode<'dtb>>::deserialize(&child, child_cx)?
				}
			}),
			ItemKind::Children => child_match_arms.extend(quote! {
				#item_name => {
					let val;
					(val, *cursor) = ::devicetree::DeserializeNode::deserialize(&child, child_cx)?;
					<#ty as ::devicetree::PushDeserializedNode>::push_node(&mut this.#field_name, val, child_cx)?;
				}
			}),
			ItemKind::ChildrenRest => {
				assert!(children_rest_stmts.is_none(), "multiple fields with attribute `#[dt_children(rest)]`");
				children_rest_stmts = Some(quote! {
					let val;
					(val, *cursor) = ::devicetree::DeserializeNode::deserialize(&child, child_cx)?;
					<#ty as ::devicetree::PushDeserializedNode>::push_node(&mut this.#field_name, val, child_cx)?;
				});
			}
		}
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

	let self_stmts = start_cursor_fields
		.into_iter()
		.map(|field| {
			quote! {
				this.#field = ::core::option::Option::Some(blob_node.start_cursor());
			}
		})
		.chain(name_fields.into_iter().map(|field| {
			quote! {
				this.#field = ::core::convert::From::from(blob_node.name()?);
			}
		}))
		.chain(unit_address_fields.into_iter().map(|field| {
			quote! {
				this.#field = blob_node.split_name()?.1.map(::core::convert::From::from);
			}
		}))
		.collect::<TokenStream>();

	let cx_deserialize_node = |child_stmts| {
		quote! {
			let (_, cursor) = cx.deserialize_node(
				blob_node,
				|name, prop| {
					match name {
						#prop_match_arms
						_ => (),
					}
					Ok(())
				},
				|child, child_cx, cursor| {
					#child_stmts
				},
			)?;
		}
	};
	let deserialize_stmts = if child_match_arms.is_empty() {
		if let Some(children_rest_stmts) = children_rest_stmts {
			cx_deserialize_node(quote! {
				#children_rest_stmts
				Ok(())
			})
		} else {
			// No children need to be parsed
			quote! {
				let mut items = blob_node.items();
				while let ::core::option::Option::Some(::devicetree::blob::Item::Property(prop)) =
					::devicetree::fallible_iterator::FallibleIterator::next(&mut items)?
				{
					match prop.name()? {
						#prop_match_arms
						_ => (),
					}
				}
				let cursor = items.end_cursor()?;
			}
		}
	} else {
		let children_rest_stmts = children_rest_stmts.unwrap_or_default();
		cx_deserialize_node(quote! {
			match child.split_name()?.0 {
				#child_match_arms
				_ => {
					#children_rest_stmts
				}
			}
			Ok(())
		})
	};
	quote! {
		impl #impl_generics ::devicetree::DeserializeNode<'dtb> for #name #ty_generics #where_clause {
			fn deserialize(
				blob_node: &::devicetree::blob::Node<'dtb>,
				cx: ::devicetree::NodeContext<'_>,
			) -> ::devicetree::Result<(Self, ::devicetree::blob::Cursor)> {
				let mut this: Self = ::core::default::Default::default();
				#self_stmts
				#deserialize_stmts
				::devicetree::Result::Ok((this, cursor))
			}
		}
	}
	.into()
}

fn field_to_node_name(name: String) -> String {
	if name == "device_type" {
		return name;
	}
	let start_hash = if name.ends_with("_cells") { "#" } else { "" };
	format!("{start_hash}{}", name.replace('_', "-"))
}

fn parse_field_attrs(
	attrs: &[Attribute],
	mut field_name: impl FnMut() -> String,
) -> Option<(ItemKind, Option<String>)> {
	let mut relevant_attrs = attrs.iter().filter_map(|attr| {
		let mut panic_invalid = |attr_name| -> ! {
			if attr_name == "dt_self" {
				panic!(
					"invalid attribute on field `{}`: `{}`
Valid forms are:
- `#[dt_self(start_cursor)]`
- `#[dt_self(name)]`
- `#[dt_self(unit_address)]`",
					field_name(),
					attr.to_token_stream(),
				);
			}
			let extra_forms = if attr_name == "dt_children" {
				"\n- `#[dt_children(rest)]`"
			} else {
				""
			};
			panic!(
				"invalid attribute on field `{}`: `{}`
Valid forms are:
- `#[{attr_name}]`
- `#[{attr_name} = \"<item name>\"]`{extra_forms}",
				field_name(),
				attr.to_token_stream(),
			)
		};

		let (path, value_lit) = match &attr.meta {
			Meta::Path(path) => (path, None),
			Meta::List(list) => (&list.path, None),
			Meta::NameValue(name_value) => {
				let Expr::Lit(ref value_lit) = name_value.value else {
					panic_invalid(&name_value.path.get_ident()?.to_string())
				};
				(&name_value.path, Some(&value_lit.lit))
			}
		};
		let attr_name = path.get_ident()?.to_string();

		let mut rest = false;
		if let Meta::List(ref list) = attr.meta {
			match &attr_name[..] {
				"dt_self" => {
					let mut kind = None;
					list.parse_nested_meta(|meta| {
						if meta.path.is_ident("start_cursor") {
							kind = Some(ItemKind::SelfStartCursor);
						} else if meta.path.is_ident("name") {
							kind = Some(ItemKind::SelfName);
						} else if meta.path.is_ident("unit_address") {
							kind = Some(ItemKind::SelfUnitAddress);
						}
						Ok(())
					})
					.unwrap();
					return Some((kind.unwrap_or_else(|| panic_invalid(&attr_name)), None));
				}
				"dt_property" | "dt_child" => panic_invalid(&attr_name),
				"dt_children" => list
					.parse_nested_meta(|meta| {
						if meta.path.is_ident("rest") {
							rest = true;
							return Ok(());
						}
						panic_invalid(&attr_name);
					})
					.unwrap(),
				_ => return None,
			}
		}
		let kind = match &attr_name[..] {
			"dt_property" => ItemKind::Property,
			"dt_child" => ItemKind::Child,
			"dt_children" if rest => ItemKind::ChildrenRest,
			"dt_children" => ItemKind::Children,
			_ => return None,
		};

		let item_name = match value_lit {
			None => None,
			Some(Lit::Str(name)) => {
				let name = name.value();
				assert!(
					!name.contains('@'),
					"item name of field `{}` contains unit address",
					field_name()
				);
				Some(name)
			}
			Some(_) => panic_invalid(&attr_name),
		};
		Some((kind, item_name))
	});
	let ret = relevant_attrs.next()?;
	assert!(
		relevant_attrs.next().is_none(),
		"duplicate attributes on field `{}`",
		field_name()
	);
	Some(ret)
}
