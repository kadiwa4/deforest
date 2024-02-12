use proc_macro2::{Literal, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{
	punctuated::Punctuated, Attribute, Expr, ExprLit, GenericParam, ItemStruct, Lit, Meta,
	MetaList, MetaNameValue, Token,
};

#[derive(Clone, Copy)]
enum ItemKind {
	StartCursor,
	Name,
	UnitAddress,
	Property,
	Child,
	Children,
	ChildrenRest,
}

/// Derive macro generating an impl of the trait `DeserializeNode`.
///
/// Requires an implementation of `Default`.
///
/// Attribute syntax:
/// - `#[dt(start_cursor)]`
/// - `#[dt(name)]`
/// - `#[dt(unit_address)]`
/// - `#[dt(property)]`
/// - `#[dt(property = \"<property name>\")]`
/// - `#[dt(child)]`
/// - `#[dt(child = \"<node name>\")]`
/// - `#[dt(children)]`
/// - `#[dt(children = \"<node name>\")]`
/// - `#[dt(children(rest))]`
///
/// The default item name is the field name with undescores replaced by hyphens
/// (and a `#` prepended in case the name ends with `_cells`), except
/// `device_type`, which uses an underscore.
/// The unit address is ignored.
///
/// - `#[dt(start_cursor)]` stores a cursor to the containing node in that field
///   (type `Option<Cursor>`).
/// - `#[dt(name)]` stores the containing node's entire name in that field
///   (type `T where T: From<&'dtb str>`).
/// - `#[dt(unit_address)]` stores the containing node's unit address in that
///   field (type `Option<T> where T: From<&'dtb str>`).
///
/// - `#[dt(property)]` (default) uses `DeserializeProperty`
/// - `#[dt(child)]` uses `DeserializeNode`
/// - `#[dt(children)]` uses `PushDeserializedNode` to collect items of type
///   `Self::Node`; it is similar to `Extend<Self::Node>`
///
/// `DeserializeNode::deserialize` is always used with an appropriate
/// `NodeContext`.
///
/// The lifetime `'dtb` (if it exists) is special because it will be used for
/// the `DeserializeNode<'dtb>` implementation.
#[proc_macro_derive(DeserializeNode, attributes(dt))]
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
			ItemKind::StartCursor => {
				start_cursor_fields.push(field_name);
				continue;
			}
			ItemKind::Name => {
				name_fields.push(field_name);
				continue;
			}
			ItemKind::UnitAddress => {
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
			ItemKind::StartCursor | ItemKind::Name | ItemKind::UnitAddress => unreachable!(),
			ItemKind::Property => {
				prop_match_arms.extend(quote! {
					#item_name => {
						this.#field_name = <#ty as ::deforest::DeserializeProperty<'dtb>>::deserialize(prop, cx)?
					}
				});
			},
			ItemKind::Child => child_match_arms.extend(quote! {
				#item_name => {
					(this.#field_name, *cursor) = <#ty as ::deforest::DeserializeNode<'dtb>>::deserialize(&child, child_cx)?
				}
			}),
			ItemKind::Children => child_match_arms.extend(quote! {
				#item_name => {
					let val;
					(val, *cursor) = ::deforest::DeserializeNode::deserialize(&child, child_cx)?;
					<#ty as ::deforest::PushDeserializedNode>::push_node(&mut this.#field_name, val, child_cx)?;
				}
			}),
			ItemKind::ChildrenRest => {
				assert!(children_rest_stmts.is_none(), "multiple fields with attribute `#[dt(children(rest))]`");
				children_rest_stmts = Some(quote! {
					let val;
					(val, *cursor) = ::deforest::DeserializeNode::deserialize(&child, child_cx)?;
					<#ty as ::deforest::PushDeserializedNode>::push_node(&mut this.#field_name, val, child_cx)?;
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
				while let ::core::option::Option::Some(::deforest::blob::Item::Property(prop)) =
					::deforest::fallible_iterator::FallibleIterator::next(&mut items)?
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
		impl #impl_generics ::deforest::DeserializeNode<'dtb> for #name #ty_generics #where_clause {
			fn deserialize(
				blob_node: &::deforest::blob::Node<'dtb>,
				cx: ::deforest::NodeContext<'_>,
			) -> ::deforest::Result<(Self, ::deforest::blob::Cursor)> {
				let mut this: Self = ::core::default::Default::default();
				#self_stmts
				#deserialize_stmts
				::deforest::Result::Ok((this, cursor))
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
	field_name: impl Fn() -> String,
) -> Option<(ItemKind, Option<String>)> {
	let mut relevant_attrs = attrs
		.iter()
		.filter(|&attr| attr.path().get_ident().is_some_and(|i| *i == "dt"));
	let attr = relevant_attrs.next()?;
	assert!(
		relevant_attrs.next().is_none(),
		"more than one attribute on field `{}`",
		field_name()
	);
	let panic_invalid = || -> ! {
		panic!(
			"invalid attribute on field `{}`: `{}`
Valid forms are:
- `#[dt(start_cursor)]`
- `#[dt(name)]`
- `#[dt(unit_address)]`
- `#[dt(property)]`
- `#[dt(property = \"<property name>\")]`
- `#[dt(child)]`
- `#[dt(child = \"<node name>\")]`
- `#[dt(children)]`
- `#[dt(children = \"<node name>\")]`
- `#[dt(children(rest))]`",
			field_name(),
			attr.to_token_stream(),
		)
	};

	let parse_item_name = |nv: MetaNameValue| -> String {
		let Expr::Lit(ExprLit {
			lit: Lit::Str(ref lit),
			..
		}) = nv.value
		else {
			panic_invalid();
		};
		assert!(
			lit.suffix().is_empty(),
			"item name literal of field `{}` has suffix",
			field_name()
		);
		let name = lit.value();
		assert!(
			!name.contains('@'),
			"item name of field `{}` contains unit address",
			field_name()
		);
		name
	};

	let meta = attr.meta.require_list().ok().and_then(meta_list_get_single);
	let meta = meta.unwrap_or_else(|| panic_invalid());
	let meta_name = meta.path().get_ident()?.to_string();

	match &meta_name[..] {
		"start_cursor" | "name" | "unit_address" => {
			if !matches!(meta, Meta::Path(_)) {
				panic_invalid();
			}
			let kind = match &meta_name[..] {
				"start_cursor" => ItemKind::StartCursor,
				"name" => ItemKind::Name,
				"unit_address" => ItemKind::UnitAddress,
				_ => unreachable!(),
			};
			Some((kind, None))
		}
		"property" | "child" => {
			let item_name = match meta {
				Meta::Path(_) => None,
				Meta::List(_) => panic_invalid(),
				Meta::NameValue(nv) => Some(parse_item_name(nv)),
			};
			let kind = match &meta_name[..] {
				"property" => ItemKind::Property,
				"child" => ItemKind::Child,
				_ => unreachable!(),
			};
			Some((kind, item_name))
		}
		"children" => match meta {
			Meta::Path(_) => Some((ItemKind::Children, None)),
			Meta::List(list) => {
				if !meta_list_get_single(&list)
					.as_ref()
					.and_then(|i| i.path().get_ident())
					.is_some_and(|i| *i == "rest")
				{
					panic_invalid();
				}
				Some((ItemKind::ChildrenRest, None))
			}
			Meta::NameValue(nv) => Some((ItemKind::Children, Some(parse_item_name(nv)))),
		},
		_ => panic_invalid(),
	}
}

fn meta_list_get_single(list: &MetaList) -> Option<Meta> {
	let list = list.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated);
	let mut iter = list.expect("invalid attribute").into_iter();
	iter.next().filter(|_| iter.next().is_none())
}
