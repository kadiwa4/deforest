use core::{cmp::Ordering, mem::size_of};

use crate::{
	blob::{Devicetree, Error, Item, Node, Property, Result},
	util,
};

pub(super) const TOKEN_SIZE: u32 = 4;

/// A parsed token from the [`Devicetree`] blob's struct block.
///
/// Does not directly correspond to a 4-byte token from the blob.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Token<'dtb> {
	BeginNode(Node<'dtb>),
	EndNode,
	Property(Property<'dtb>),
}

impl<'dtb> Token<'dtb> {
	/// Returns an item if this is a `BeginNode` or `Property` token.
	pub fn into_item(self) -> Option<Item<'dtb>> {
		match self {
			Self::BeginNode(node) => Some(Item::Child(node)),
			Self::EndNode => None,
			Self::Property(prop) => Some(Item::Property(prop)),
		}
	}
}

/// A position inside the [`Devicetree`] blob's struct block.
///
/// Can be obtained from [`Node::content_cursor`] and advanced using
/// [`Devicetree::next_token`].
///
/// Do not compare cursors from different devicetrees.
#[derive(Clone, Copy, Debug, Eq)]
pub struct Cursor {
	pub(super) depth: u32,
	pub(super) offset: u32,
}

impl PartialOrd for Cursor {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(Ord::cmp(self, other))
	}
}

impl Ord for Cursor {
	fn cmp(&self, other: &Self) -> Ordering {
		let res = Ord::cmp(&self.offset, &other.offset);
		if res == Ordering::Equal {
			debug_assert_eq!(self.depth, other.depth);
		}
		res
	}
}

impl PartialEq for Cursor {
	fn eq(&self, other: &Self) -> bool {
		Ord::cmp(self, other) == Ordering::Equal
	}
}

impl Cursor {
	fn increase_offset(&mut self, add: u32, blob: &[u8]) -> Result<()> {
		// basically u32::div_ceil(offset + add, 4) * 4
		let offset = u32::checked_add(self.offset, add)
			.and_then(|offset| u32::checked_add(offset, TOKEN_SIZE - 1))
			.ok_or(Error::UnexpectedEnd)?
			& TOKEN_SIZE.wrapping_neg();

		blob.get(offset as usize..).ok_or(Error::UnexpectedEnd)?;
		self.offset = offset;
		Ok(())
	}
}

#[repr(u32)]
enum RawToken {
	BeginNode = 1_u32.to_be(),
	EndNode = 2_u32.to_be(),
	Prop = 3_u32.to_be(),
	Nop = 4_u32.to_be(),
	End = 9_u32.to_be(),
}

impl Devicetree {
	/// The devicetree's root node.
	pub fn root_node(&self) -> Result<Node<'_>> {
		self.struct_blob()?;

		let mut cursor = Cursor {
			depth: 0,
			offset: u32::from_be(self.header().off_dt_struct),
		};
		match self.next_token(&mut cursor)? {
			Some(Token::BeginNode(node)) if node.name.is_empty() => Ok(node),
			_ => Err(Error::InvalidRootNode),
		}
	}

	/// Returns the token pointed to by the cursor and advance the cursor.
	pub fn next_token(&self, cursor: &mut Cursor) -> Result<Option<Token<'_>>> {
		const PROP_HEADER_SIZE: usize = size_of::<PropHeader>();

		#[repr(C)]
		struct PropHeader {
			len: u32,
			nameoff: u32,
		}

		let blob = self.blob_u8();
		loop {
			let token = self.next_raw(cursor)?.ok_or(Error::UnexpectedEnd)?;
			let offset = cursor.offset as usize;

			let token = match token {
				RawToken::BeginNode => {
					let name = &blob[cursor.offset as usize..];
					let name = util::get_c_str(name)?;

					cursor.increase_offset(name.len() as u32 + 1, blob)?;
					cursor.depth += 1;
					Token::BeginNode(Node {
						dt: self,
						name,
						contents: *cursor,
					})
				}
				RawToken::EndNode => {
					let depth =
						u32::checked_sub(cursor.depth, 1).ok_or(Error::UnexpectedEndNodeToken)?;
					cursor.depth = depth;

					Token::EndNode
				}
				RawToken::Prop => {
					let header = util::slice_get_with_len(blob, offset, PROP_HEADER_SIZE)
						.ok_or(Error::InvalidPropertyHeader)?;

					let header = unsafe { &*(header as *const _ as *const PropHeader) };
					let name_blob = self
						.strings_blob()?
						.get(u32::from_be(header.nameoff) as usize..)
						.ok_or(Error::InvalidString)?;

					cursor.offset += PROP_HEADER_SIZE as u32;
					let offset = cursor.offset as usize;

					let len = u32::from_be(header.len);
					let value = util::slice_get_with_len(blob, offset, len as usize)
						.ok_or(Error::InvalidPropertyHeader)?;

					cursor.increase_offset(len, blob)?;

					Token::Property(Property { name_blob, value })
				}
				RawToken::Nop => continue,
				RawToken::End => {
					if cursor.depth == 0 {
						return Ok(None);
					} else {
						return Err(Error::UnexpectedEndToken);
					}
				}
			};
			return Ok(Some(token));
		}
	}

	fn next_raw(&self, cursor: &mut Cursor) -> Result<Option<RawToken>> {
		const BEGIN_NODE: u32 = RawToken::BeginNode as u32;
		const END_NODE: u32 = RawToken::EndNode as u32;
		const PROP: u32 = RawToken::Prop as u32;
		const NOP: u32 = RawToken::Nop as u32;
		const END: u32 = RawToken::End as u32;

		let offset = cursor.offset as usize;
		let Some(token) = util::slice_get_with_len(self.blob_u8(), offset, TOKEN_SIZE as usize)
		else {
			return Ok(None)
		};
		let token = unsafe { *(token as *const _ as *const u32) };

		cursor.offset += TOKEN_SIZE;
		let token = match token {
			BEGIN_NODE => RawToken::BeginNode,
			END_NODE => RawToken::EndNode,
			PROP => RawToken::Prop,
			NOP => RawToken::Nop,
			END => RawToken::End,
			_ => return Err(Error::UnknownToken),
		};
		Ok(Some(token))
	}
}
