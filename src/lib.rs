#![cfg_attr(not(test), no_std)]
#![feature(slice_ptr_get, unchecked_shifts)]

mod segment;

mod index;
pub use index::*;

#[cfg(test)]
mod tests;

use crate::segment::Segment;
use core::{cmp::min, fmt, num::NonZero, ptr::NonNull};
use thiserror::Error;

fn decompose_bitmap_index(index: usize) -> (usize, usize) {
    let segment_index = index.unbounded_shr(Segment::BITS_SHIFT);
    let segment_bit_index = index & 1usize.wrapping_shl(Segment::BITS_SHIFT).wrapping_sub(1);

    (segment_index, segment_bit_index)
}

fn bitmap_get_bit(index: usize, bitmap: &BitMap) -> Result<bool, BitMapError> {
    if index >= bitmap.valid_bit_length {
        return Err(BitMapError::OutOfBounds);
    }

    let (segment_index, segment_bit_index) = decompose_bitmap_index(index);

    // Safety: `self` is checked to be less than `bitmap.bit_len`.
    let segment = unsafe { bitmap.segments.get_unchecked(segment_index) };
    let value = segment.get_bit(segment_bit_index);

    Ok(value)
}

fn bitmap_get_bits(
    mut start_bit_inclusive: usize,
    end_bit_exclusive: usize,
    bitmap: &BitMap,
) -> Result<bool, BitMapError> {
    if end_bit_exclusive > bitmap.valid_bit_length {
        return Err(BitMapError::OutOfBounds);
    }

    let segment_start = start_bit_inclusive >> Segment::BITS_SHIFT;
    let segment_count =
        ((end_bit_exclusive + (Segment::BITS - 1)) >> Segment::BITS_SHIFT) - segment_start;

    let is_all_set = bitmap
        .segments
        .iter()
        .enumerate()
        .skip(segment_start)
        .take(segment_count)
        .all(|(segment_index, segment)| {
            let bit_index = segment_index * Segment::BITS;
            let segment_bits_start = start_bit_inclusive - bit_index;
            let segment_bits_end = min(end_bit_exclusive - bit_index, Segment::BITS);
            let segment_bits = segment_bits_start..segment_bits_end;

            start_bit_inclusive += segment_bits.len();

            segment.get_bits(segment_bits)
        });

    Ok(is_all_set)
}

fn bitmap_set_bit(index: usize, bitmap: &mut BitMap, set: bool) -> Result<(), BitMapError> {
    if index >= bitmap.valid_bit_length {
        return Err(BitMapError::OutOfBounds);
    }

    let (segment_index, segment_bit_index) = decompose_bitmap_index(index);

    // Safety: `self`  is checked to be less than `bitmap.bit_len`.
    let segment = unsafe { bitmap.segments.get_unchecked_mut(segment_index) };

    if set {
        segment.set_bit(segment_bit_index);
    } else {
        segment.unset_bit(segment_bit_index);
    }

    Ok(())
}

fn bitmap_set_bits(
    mut start_bit_inclusive: usize,
    end_bit_exclusive: usize,
    bitmap: &mut BitMap,
    set: bool,
) -> Result<(), BitMapError> {
    if end_bit_exclusive > bitmap.valid_bit_length {
        return Err(BitMapError::OutOfBounds);
    }

    let segment_start = start_bit_inclusive >> Segment::BITS_SHIFT;
    let segment_count =
        ((end_bit_exclusive + (Segment::BITS - 1)) >> Segment::BITS_SHIFT) - segment_start;

    bitmap
        .segments
        .iter_mut()
        .enumerate()
        .skip(segment_start)
        .take(segment_count)
        .for_each(|(segment_index, segment)| {
            let bit_index = segment_index * Segment::BITS;
            let segment_bits_start = start_bit_inclusive - bit_index;
            let segment_bits_end = min(end_bit_exclusive - bit_index, Segment::BITS);
            let segment_bits = segment_bits_start..segment_bits_end;

            start_bit_inclusive += segment_bits.len();

            if set {
                segment.set_bits(segment_bits);
            } else {
                segment.unset_bits(segment_bits);
            }
        });

    Ok(())
}

fn bitmap_set_next_free_inbetween(bitmap: &mut BitMap, size: NonZero<usize>) -> Option<usize> {
    // This function assumes that finding `size` free bits in any individual segment
    // failed; so, this function will *only* search in-between segments for free bit
    // runs.

    let mut start_index = Option::<(usize, usize)>::None;
    let mut current_run = 0usize;
    let mut current_index = 0usize;

    loop {
        let segment = bitmap.segments.get(current_index)?;
        let leading_free = segment.leading_free() as usize;
        let trailing_free = segment.trailing_free() as usize;

        match (current_run, leading_free, trailing_free) {
            (0, 0, _) => {
                start_index = None;
                current_run = 0;
            }

            (0, leading_free, _) => {
                start_index = Some((current_index, Segment::BITS - leading_free));
                current_run = leading_free;
            }

            (_, _, 0) => {
                start_index = None;
                current_run = 0;
            }

            (_, _, trailing_free) if trailing_free >= (size.get() - current_run) => {
                // `current_run` is complete; don't update any state, just break the loop to
                // return.
                break;
            }

            (_, _, Segment::BITS) => {
                current_run += Segment::BITS;
            }

            (_, _, _) => {
                unreachable!()
            }
        }

        current_index += 1;
    }

    start_index
        .map(|(start_index, segment_start_bit_index)| {
            (start_index * Segment::BITS) + segment_start_bit_index
        })
        .inspect(|start_bit_index| {
            // Safety: Bit range is checked to be within bounds and unused.
            unsafe {
                bitmap_set_bits(
                    *start_bit_index,
                    *start_bit_index + size.get(),
                    bitmap,
                    true,
                )
                .unwrap_unchecked();
            }
        })
}

#[derive(Debug, Error)]
pub enum BitMapError {
    #[error("index was out of bounds")]
    OutOfBounds,
}

pub struct BitMap<'a> {
    segments: &'a mut [Segment],
    valid_bit_length: usize,
}

impl<'a> BitMap<'a> {
    pub fn new(bits: &'a mut [usize], valid_bit_length: usize) -> Self {
        // Clear the bitmap.
        bits.fill(0);

        // Safety: `Segment` has the same alignment, size, and bit validity as `usize.`
        let segments = unsafe {
            core::slice::from_raw_parts_mut::<'a>(bits.as_mut_ptr().cast::<Segment>(), bits.len())
        };

        Self {
            segments,
            valid_bit_length,
        }
    }

    /// # Safety
    ///
    /// - `bits` must be [convertible to a mutable reference](https://doc.rust-lang.org/nightly/core/ptr/index.html#pointer-to-reference-conversion),
    ///   except that the data may be unitialized (it will be zeroed).
    pub unsafe fn new_from_ptr(bits: NonNull<[usize]>, valid_bit_length: usize) -> Self {
        // Safety: Caller is required to maintain safety invariants.
        unsafe {
            core::ptr::write_bytes(bits.as_mut_ptr(), 0, bits.len() * size_of::<usize>());
        }

        // Safety:
        // - `bits` has been statically initialized to zeros.
        // - Caller is required to maintain other invariants.
        let segments = unsafe {
            core::slice::from_raw_parts_mut::<'a>(bits.as_mut_ptr().cast::<Segment>(), bits.len())
        };

        Self {
            segments,
            valid_bit_length,
        }
    }

    pub fn get<I: BitMapIndex>(&self, index: I) -> Result<bool, BitMapError> {
        index.get(self)
    }

    pub fn set<I: BitMapIndex>(&mut self, index: I) -> Result<(), BitMapError> {
        index.set(self)
    }

    pub fn unset<I: BitMapIndex>(&mut self, index: I) -> Result<(), BitMapError> {
        index.unset(self)
    }

    pub fn next_free(&mut self, size: NonZero<usize>) -> Option<usize> {
        match size {
            NonZero::<usize>::MIN => {
                self.segments
                    .iter_mut()
                    .enumerate()
                    .find_map(|(index, segment)| {
                        segment
                            .next_free(NonZero::<u32>::MIN)
                            .map(|bit_index| (index * Segment::BITS) + (bit_index as usize))
                    })
            }

            size if size.get() < Segment::BITS => self
                .segments
                .iter_mut()
                .enumerate()
                .find_map(|(index, segment)| {
                    segment
                        .next_free(unsafe { NonZero::<u32>::try_from(size).unwrap_unchecked() })
                        .map(|bit_index| (index * Segment::BITS) + (bit_index as usize))
                })
                .or_else(|| bitmap_set_next_free_inbetween(self, size)),

            size if size.get() == Segment::BITS => self
                .segments
                .iter_mut()
                .enumerate()
                .find_map(|(index, segment)| {
                    segment.is_empty().then(|| {
                        segment.set_full();
                        index * Segment::BITS
                    })
                })
                .or_else(|| bitmap_set_next_free_inbetween(self, size)),

            size => bitmap_set_next_free_inbetween(self, size),
        }
    }
}

impl PartialEq<&[usize]> for BitMap<'_> {
    fn eq(&self, other: &&[usize]) -> bool {
        // Safety: `Segment` is `#[repr(transparent)]` over `usize`.
        let inner = unsafe {
            core::slice::from_raw_parts(self.segments.as_ptr().cast::<usize>(), self.segments.len())
        };

        inner.eq(*other)
    }
}

impl fmt::Debug for BitMap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BitMap")
            .field("Bit Length", &self.valid_bit_length)
            .field("Bits", &self.segments)
            .finish()
    }
}

impl fmt::Binary for BitMap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bitmap_set = f.debug_set();

        self.segments.iter().for_each(|segment| {
            bitmap_set.entry(&format_args!("{segment:b}"));
        });

        bitmap_set.finish()
    }
}
