#![cfg_attr(not(test), no_std)]

use core::{cmp::min, fmt, ops::Range};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum BitMapError {
    #[error("index was out of bounds")]
    OutOfBounds,
}

#[repr(transparent)]
#[derive(Clone, Copy)]
struct Segment(usize);

impl Segment {
    pub const BITS: usize = usize::BITS as usize;
    pub const BITS_SHIFT: u32 = usize::BITS.trailing_zeros();

    pub fn get_bit(self, index: usize) -> Result<bool, BitMapError> {
        if index >= Segment::BITS {
            return Err(BitMapError::OutOfBounds);
        }

        Ok((self.0 & (1 << index)) > 0)
    }

    pub fn set_bit(&mut self, index: usize) -> Result<(), BitMapError> {
        if index >= Segment::BITS {
            return Err(BitMapError::OutOfBounds);
        }

        self.0 |= 1 << index;

        Ok(())
    }

    pub fn unset_bit(&mut self, index: usize) -> Result<(), BitMapError> {
        if index >= Segment::BITS {
            return Err(BitMapError::OutOfBounds);
        }

        self.0 &= !(1 << index);

        Ok(())
    }

    pub fn set_bits(&mut self, bits: Range<usize>) -> Result<(), BitMapError> {
        if bits.end > Segment::BITS {
            return Err(BitMapError::OutOfBounds);
        }

        let mask = 1usize.unbounded_shl(bits.len() as u32).wrapping_sub(1);

        #[cfg(test)]
        println!("BITS {}..{}   MASK {mask:b}", bits.start, bits.end);

        self.0 |= mask.unbounded_shl(bits.start as u32);

        Ok(())
    }

    pub fn unset_bits(&mut self, bits: Range<usize>) -> Result<(), BitMapError> {
        if bits.end > Segment::BITS {
            return Err(BitMapError::OutOfBounds);
        }

        let mask = 1usize.unbounded_shl(bits.len() as u32).wrapping_sub(1);
        self.0 &= !mask.unbounded_shl(bits.start as u32);

        Ok(())
    }

    pub fn next_free(self) -> Option<usize> {
        match self.0.leading_ones() {
            free_bit_index @ 0..usize::BITS => Some(free_bit_index as usize),
            usize::BITS => None,

            // Safety: `usize::leading_ones()` cannot overflow `usize::BITS`.
            _ => unsafe { core::hint::unreachable_unchecked() },
        }
    }
}

impl fmt::Debug for Segment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

struct DecomposedIndex {
    segment_index: usize,
    segment_bit_index: usize,
}

pub struct BitMap<'a> {
    bits: &'a mut [Segment],
    bit_len: usize,
}

impl BitMap<'_> {
    fn decompose_bitmap_index(&self, index: usize) -> DecomposedIndex {
        let segment_index = index.unbounded_shr(Segment::BITS_SHIFT);
        let segment_bit_index = index & 1usize.wrapping_shl(Segment::BITS_SHIFT).wrapping_sub(1);

        DecomposedIndex {
            segment_index,
            segment_bit_index,
        }
    }

    pub fn get_bit(&self, index: usize) -> Result<bool, BitMapError> {
        if index >= self.bit_len {
            return Err(BitMapError::OutOfBounds);
        }

        let index = self.decompose_bitmap_index(index);
        self.bits[index.segment_index].get_bit(index.segment_bit_index)
    }

    pub fn set_bit(&mut self, index: usize) -> Result<(), BitMapError> {
        if index >= self.bit_len {
            return Err(BitMapError::OutOfBounds);
        }

        let index = self.decompose_bitmap_index(index);
        self.bits[index.segment_index].set_bit(index.segment_bit_index)?;

        Ok(())
    }

    pub fn unset_bit(&mut self, index: usize) -> Result<(), BitMapError> {
        if index >= self.bit_len {
            return Err(BitMapError::OutOfBounds);
        }

        let index = self.decompose_bitmap_index(index);
        self.bits[index.segment_index].unset_bit(index.segment_bit_index)?;

        Ok(())
    }

    pub fn set_bits(&mut self, mut bits: Range<usize>) -> Result<(), BitMapError> {
        if bits.end > self.bit_len {
            return Err(BitMapError::OutOfBounds);
        }

        let segment_start = bits.start >> Segment::BITS_SHIFT;
        let segment_count =
            ((bits.end + (Segment::BITS - 1)) >> Segment::BITS_SHIFT) - segment_start;

        self.bits
            .iter_mut()
            .enumerate()
            .skip(segment_start)
            .take(segment_count)
            .map(|(index, segment)| (index * Segment::BITS, segment))
            .try_for_each(|(bit_index, segment)| {
                let segment_bits_start = bits.start - bit_index;
                let segment_bits_end = min(bits.end - bit_index, Segment::BITS);
                let segment_bits = segment_bits_start..segment_bits_end;

                bits.start += segment_bits.len();

                segment.set_bits(segment_bits)
            })
    }

    pub fn unset_bits(&mut self, mut bits: Range<usize>) -> Result<(), BitMapError> {
        if bits.end > self.bit_len {
            return Err(BitMapError::OutOfBounds);
        }

        let segment_start = bits.start >> Segment::BITS_SHIFT;
        let segment_count =
            ((bits.end + (Segment::BITS - 1)) >> Segment::BITS_SHIFT) - segment_start;

        self.bits
            .iter_mut()
            .enumerate()
            .skip(segment_start)
            .take(segment_count)
            .map(|(index, segment)| (index * Segment::BITS, segment))
            .try_for_each(|(bit_index, segment)| {
                let segment_bits_start = bits.start - bit_index;
                let segment_bits_end = min(bits.end - bit_index, Segment::BITS);
                let segment_bits = segment_bits_start..segment_bits_end;

                bits.start += segment_bits.len();

                segment.unset_bits(segment_bits)
            })
    }

    pub fn next_free(&self) -> Option<usize> {
        self.bits.iter().find_map(|segment| segment.next_free())
    }
}

impl fmt::Debug for BitMap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BitMap")
            .field("Bit Length", &self.bit_len)
            .field("Bits", &self.bits)
            .finish()
    }
}

impl fmt::Binary for BitMap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bitmap_set = f.debug_set();

        self.bits.iter().for_each(|segment| {
            bitmap_set.entry(&format_args!(
                "{:0>width$b}",
                segment.0,
                width = Segment::BITS,
            ));
        });

        bitmap_set.finish()
    }
}

#[test]
fn test() {
    unsafe {
        let memory = std::alloc::alloc(std::alloc::Layout::from_size_align_unchecked(0xC0, 0x1));
        let memory =
            std::slice::from_raw_parts_mut(memory.cast::<Segment>(), 0xC0 >> Segment::BITS_SHIFT);

        let mut bitmap = BitMap {
            bits: memory,
            bit_len: 192,
        };

        println!("{bitmap:b}");
        bitmap.set_bits(64..72).unwrap();
        println!("{bitmap:b}");
        bitmap.unset_bits(65..71).unwrap();
        println!("{bitmap:b}");
    }
}
