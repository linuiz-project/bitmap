#![cfg_attr(not(test), no_std)]
#![feature(unchecked_shifts)]

#[cfg(test)]
mod tests;

use core::{cmp::min, convert::Infallible, fmt, num::NonZero, ops::Range};
use thiserror::Error;

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct Segment(usize);

impl Segment {
    pub const BITS: usize = usize::BITS as usize;
    pub const BITS_SHIFT: u32 = usize::BITS.trailing_zeros();

    pub fn get_bit(self, index: usize) -> bool {
        debug_assert!(index < Segment::BITS);

        (self.0 & (1 << index)) > 0
    }

    pub fn set_bit(&mut self, index: usize) {
        debug_assert!(index < Segment::BITS);

        self.0 |= 1 << index;
    }

    pub fn unset_bit(&mut self, index: usize) {
        debug_assert!(index < Segment::BITS);

        self.0 &= !(1 << index);
    }

    pub fn set_bits(&mut self, bits: Range<usize>) {
        debug_assert!(bits.end <= Segment::BITS);

        self.0 |= 1usize
            .unbounded_shl(bits.len() as u32)
            .wrapping_sub(1)
            .unbounded_shl(bits.start as u32);
    }

    pub fn unset_bits(&mut self, bits: Range<usize>) {
        debug_assert!(bits.end <= Segment::BITS);

        self.0 &= !1usize
            .unbounded_shl(bits.len() as u32)
            .wrapping_sub(1)
            .unbounded_shl(bits.start as u32);
    }

    pub fn next_free(self) -> Option<u32> {
        match self.0.leading_ones() {
            free_bit_index @ 0..usize::BITS => Some(free_bit_index),
            usize::BITS => None,

            // Safety: `usize::leading_ones()` cannot overflow `usize::BITS`.
            _ => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    pub fn next_free_many(self, bit_count: NonZero<u32>) -> Option<u32> {
        let size_mask = 1usize.unbounded_shl(bit_count.get()).wrapping_sub(1);
        let mut bit_offset = self.0.trailing_ones();

        while (bit_offset + bit_count.get()) <= usize::BITS {
            // Safety: `bit_offset` is checked to less than `usize::BITS`.
            let bits = unsafe { self.0.unchecked_shr(bit_offset) };

            if (bits & size_mask) == 0 {
                return Some(bit_offset);
            } else {
                let trailing_zeros = bits.trailing_zeros();
                let offset_trailing_ones = bits.unbounded_shr(trailing_zeros).trailing_ones();

                // We want to shift off both the trailing zeros and ones (to get
                // to the next zeros to test).
                bit_offset += offset_trailing_ones + trailing_zeros;
            }
        }

        None
    }
}

impl fmt::Debug for Segment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

fn decompose_bitmap_index(index: usize) -> DecomposedIndex {
    let segment_index = index.unbounded_shr(Segment::BITS_SHIFT);
    let segment_bit_index = index & 1usize.wrapping_shl(Segment::BITS_SHIFT).wrapping_sub(1);

    DecomposedIndex {
        segment_index,
        segment_bit_index,
    }
}

pub trait BitMapIndex {
    type Output;

    fn get(&self, bitmap: &BitMap) -> Result<Self::Output, BitMapError>;
    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError>;
    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError>;
}

fn bitmap_set_bit(index: usize, bitmap: &mut BitMap, set: bool) -> Result<(), BitMapError> {
    if index >= bitmap.bit_len {
        return Err(BitMapError::OutOfBounds);
    }

    let index = decompose_bitmap_index(index);

    // Safety: `self`  is checked to be less than `bitmap.bit_len`.
    let segment = unsafe { bitmap.segments.get_unchecked_mut(index.segment_index) };

    if set {
        segment.set_bit(index.segment_bit_index);
    } else {
        segment.unset_bit(index.segment_bit_index);
    }

    Ok(())
}

impl BitMapIndex for usize {
    type Output = bool;

    fn get(&self, bitmap: &BitMap) -> Result<bool, BitMapError> {
        if *self >= bitmap.bit_len {
            return Err(BitMapError::OutOfBounds);
        }

        let index = decompose_bitmap_index(*self);

        // Safety: `self`  is checked to be less than `bitmap.bit_len`.
        let segment = unsafe { bitmap.segments.get_unchecked(index.segment_index) };
        let value = segment.get_bit(index.segment_bit_index);

        Ok(value)
    }

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bit(*self, bitmap, true)
    }

    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bit(*self, bitmap, false)
    }
}

fn bitmap_set_bits(
    mut start_bit_inclusive: usize,
    end_bit_exclusive: usize,
    bitmap: &mut BitMap,
    set: bool,
) -> Result<(), BitMapError> {
    if end_bit_exclusive > bitmap.bit_len {
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

            #[cfg(test)]
            println!("SEG BITS {segment_bits:?}");

            start_bit_inclusive += segment_bits.len();

            if set {
                segment.set_bits(segment_bits);
            } else {
                segment.unset_bits(segment_bits);
            }
        });

    Ok(())
}

impl BitMapIndex for Range<usize> {
    type Output = Infallible;

    fn get(&self, _: &BitMap) -> Result<Self::Output, BitMapError> {
        unimplemented!()
    }

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(self.start, self.end, bitmap, true)
    }

    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(self.start, self.end, bitmap, false)
    }
}

#[derive(Debug, Error)]
pub enum BitMapError {
    #[error("index was out of bounds")]
    OutOfBounds,
}

struct DecomposedIndex {
    segment_index: usize,
    segment_bit_index: usize,
}

pub struct BitMap<'a> {
    segments: &'a mut [Segment],
    bit_len: usize,
}

impl<'a> BitMap<'a> {
    pub fn new(bits: &'a mut [usize], real_bit_len: usize) -> Self {
        // Clear the bitmap.
        bits.fill(0);

        // Safety: `Segment` has the same alignment, size, and bit validity as `usize.`
        let segments = unsafe {
            core::slice::from_raw_parts_mut::<'a>(bits.as_mut_ptr().cast::<Segment>(), bits.len())
        };

        Self {
            segments,
            bit_len: real_bit_len,
        }
    }

    pub fn get<I: BitMapIndex>(&self, index: I) -> Result<I::Output, BitMapError> {
        index.get(self)
    }

    pub fn set<I: BitMapIndex>(&mut self, index: I) -> Result<(), BitMapError> {
        index.set(self)
    }

    pub fn unset<I: BitMapIndex>(&mut self, index: I) -> Result<(), BitMapError> {
        index.unset(self)
    }

    pub fn next_free(&self, size: NonZero<usize>) -> Option<usize> {
        match size.get() {
            0 => {
                // Safety: `size` is non-zero.
                unsafe { core::hint::unreachable_unchecked() }
            }

            1 => self
                .segments
                .iter()
                .enumerate()
                .find_map(|(index, segment)| {
                    segment
                        .next_free()
                        .map(|bit_index| (index * Segment::BITS) + (bit_index as usize))
                }),

            size => {
                let mut segment_iter = self.segments.iter();
                let mut first_index = 0;
                let mut current_run = 0;

                while current_run < size {
                    let remaining_run = size - current_run;

                    let segment = segment_iter.next()?;
                    let segment_first_free_index = segment.0.count_ones();
                }

                todo!()
            }
        }
    }
}

impl fmt::Debug for BitMap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BitMap")
            .field("Bit Length", &self.bit_len)
            .field("Bits", &self.segments)
            .finish()
    }
}

impl fmt::Binary for BitMap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bitmap_set = f.debug_set();

        self.segments.iter().for_each(|segment| {
            bitmap_set.entry(&format_args!(
                "{:0>width$b}",
                segment.0,
                width = Segment::BITS,
            ));
        });

        bitmap_set.finish()
    }
}
