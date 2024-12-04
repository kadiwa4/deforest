use core::{
	cmp::Ordering,
	hash::{Hash, Hasher},
};

use zerocopy::FromBytes;

use super::{BlobError, Devicetree, DtUint, Item, Node, Property, Result};
use crate::util;

pub(super) const TOKEN_SIZE: DtUint = 4;

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
/// You can think of this as a byte offset from the blob's start address, but it
/// is a little more complicated in reality.
/// Can be obtained from [`Node::content_cursor`] and advanced using
/// [`Devicetree::next_token`].
///
/// Do not compare cursors from different devicetrees.
#[derive(Clone, Copy, Debug, Eq)]
pub struct Cursor {
	pub(super) depth: DtUint,
	pub(super) offset: DtUint,
}

impl PartialOrd for Cursor {
	#[inline]
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(Ord::cmp(self, other))
	}
}

impl Ord for Cursor {
	#[inline]
	fn cmp(&self, other: &Self) -> Ordering {
		let res = Ord::cmp(&self.offset, &other.offset);
		if res == Ordering::Equal {
			debug_assert_eq!(self.depth, other.depth);
		}
		res
	}
}

impl PartialEq for Cursor {
	#[inline]
	fn eq(&self, other: &Self) -> bool {
		Ord::cmp(self, other) == Ordering::Equal
	}
}

impl Hash for Cursor {
	#[inline]
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.offset.hash(state);
	}
}

impl Cursor {
	/// Increases the offset of the cursor to the value of `add` but rounded up
	/// to the next multiple of `TOKEN_SIZE`.
	fn increase_offset(&mut self, add: DtUint, blob: &[u8]) -> Result<()> {
		let offset = DtUint::checked_add(self.offset, add)
			.and_then(|o| o.checked_next_multiple_of(TOKEN_SIZE))
			.ok_or(BlobError::UnexpectedEnd)?;

		blob.get(offset as usize..)
			.ok_or(BlobError::UnexpectedEnd)?;
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
		// bounds check was done in Self::late_checks
		let mut cursor = Cursor {
			depth: 0,
			offset: u32::from_be(self.header().off_dt_struct) as DtUint,
		};
		match self.next_token(&mut cursor)? {
			Some(Token::BeginNode(node)) if node.name.is_empty() => Ok(node),
			_ => Err(BlobError::InvalidRootNode),
		}
	}

	/// Returns the token pointed to by the cursor and advance the cursor.
	pub fn next_token(&self, cursor: &mut Cursor) -> Result<Option<Token<'_>>> {
		#[derive(FromBytes)]
		#[repr(C)]
		struct PropHeader {
			len: u32,
			nameoff: u32,
		}

		let blob = self.blob_with_struct_block_end();
		loop {
			let token = next_raw(blob, cursor)?.ok_or(BlobError::UnexpectedEnd)?;
			let offset = cursor.offset as usize;

			let token = match token {
				RawToken::BeginNode => {
					let name = &blob[offset..];
					let name = util::get_c_str(name)?;

					cursor.increase_offset(name.len() as DtUint + 1, blob)?;
					cursor.depth += 1;
					Token::BeginNode(Node {
						dt: self,
						name,
						contents: *cursor,
					})
				}
				RawToken::EndNode => {
					let depth = cursor
						.depth
						.checked_sub(1)
						.ok_or(BlobError::UnexpectedEndNodeToken)?;
					cursor.depth = depth;

					Token::EndNode
				}
				RawToken::Prop => {
					let (header, _) = PropHeader::read_from_prefix(&blob[offset..])
						.map_err(|_| BlobError::UnexpectedEnd)?;

					let name_blob = usize::try_from(u32::from_be(header.nameoff))
						.ok()
						.and_then(|offset| self.strings_blob().get(offset..))
						.ok_or(BlobError::InvalidString)?;

					cursor.offset += size_of::<PropHeader>() as DtUint;
					let offset = cursor.offset as usize;

					let len = DtUint::try_from(u32::from_be(header.len))
						.map_err(|_| BlobError::InvalidPropertyHeader)?;
					let value = blob
						.get(offset..offset + len as usize)
						.ok_or(BlobError::InvalidPropertyHeader)?;

					cursor.increase_offset(len, blob)?;

					Token::Property(Property { name_blob, value })
				}
				RawToken::Nop => continue,
				RawToken::End => {
					if cursor.depth == 0 {
						return Ok(None);
					} else {
						return Err(BlobError::UnexpectedEndToken);
					}
				}
			};
			return Ok(Some(token));
		}
	}
}

fn next_raw(blob: &[u8], cursor: &mut Cursor) -> Result<Option<RawToken>> {
	const BEGIN_NODE: u32 = RawToken::BeginNode as u32;
	const END_NODE: u32 = RawToken::EndNode as u32;
	const PROP: u32 = RawToken::Prop as u32;
	const NOP: u32 = RawToken::Nop as u32;
	const END: u32 = RawToken::End as u32;

	let offset = cursor.offset as usize;
	let Some(&token) = blob[offset..].first_chunk::<{ TOKEN_SIZE as usize }>() else {
		return Ok(None);
	};

	cursor.offset += TOKEN_SIZE;
	let token = match u32::from_ne_bytes(token) {
		BEGIN_NODE => RawToken::BeginNode,
		END_NODE => RawToken::EndNode,
		PROP => RawToken::Prop,
		NOP => RawToken::Nop,
		END => RawToken::End,
		_ => return Err(BlobError::UnknownToken),
	};
	Ok(Some(token))
}
