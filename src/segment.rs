use core::{num::NonZero, ops::Range};

#[repr(transparent)]
#[derive(Default, Clone, Copy, PartialEq, Eq)]
pub struct Segment(usize);

impl Segment {
    pub const BITS: usize = usize::BITS as usize;
    pub const BITS_SHIFT: u32 = usize::BITS.trailing_zeros();

    #[cfg(test)]
    pub const fn new(bits: usize) -> Self {
        Self(bits)
    }

    pub fn leading_free(self) -> u32 {
        self.0.leading_zeros()
    }

    pub fn trailing_free(self) -> u32 {
        self.0.trailing_zeros()
    }

    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub fn is_full(self) -> bool {
        self.0 == usize::MAX
    }

    pub fn get_bit(self, index: usize) -> bool {
        debug_assert!(index < Segment::BITS);

        (self.0 & (1 << index)) > 0
    }

    pub fn get_bits(self, bits: Range<usize>) -> bool {
        debug_assert!(bits.end <= Segment::BITS);

        let mask = 1usize
            .unbounded_shl(bits.len() as u32)
            .wrapping_sub(1)
            .unbounded_shl(bits.start as u32);

        (self.0 & mask) == mask
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

        if bits.len() == Self::BITS {
            self.set_full();
        } else {
            let mask = 1usize
                .unbounded_shl(bits.len() as u32)
                .wrapping_sub(1)
                .unbounded_shl(bits.start as u32);

            self.0 |= mask;
        }
    }

    pub fn unset_bits(&mut self, bits: Range<usize>) {
        debug_assert!(bits.end <= Segment::BITS);

        if bits.len() == Self::BITS {
            self.set_empty();
        } else {
            let mask = !1usize
                .unbounded_shl(bits.len() as u32)
                .wrapping_sub(1)
                .unbounded_shl(bits.start as u32);

            self.0 &= mask;
        }
    }

    pub fn set_empty(&mut self) {
        debug_assert!(self.is_full());

        self.0 = 0;
    }

    pub fn set_full(&mut self) {
        debug_assert!(self.is_empty());

        self.0 = usize::MAX;
    }

    pub fn next_free(&mut self, bit_count: NonZero<u32>) -> Option<u32> {
        if self.is_full() {
            None
        } else if bit_count == NonZero::<u32>::MIN {
            match self.0.trailing_ones() {
                free_bit_index @ 0..usize::BITS => {
                    self.set_bit(free_bit_index as usize);

                    Some(free_bit_index)
                }

                usize::BITS => None,

                // Safety: `usize::leading_ones()` cannot overflow `usize::BITS`.
                _ => unsafe { core::hint::unreachable_unchecked() },
            }
        } else {
            let size_mask = 1usize.unbounded_shl(bit_count.get()).wrapping_sub(1);
            let mut bit_offset = self.0.trailing_ones();

            while (bit_offset + bit_count.get()) <= usize::BITS {
                let bits = self.0 >> bit_offset;

                if (bits & size_mask) == 0 {
                    self.0 |= size_mask << bit_offset;

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
}

impl core::fmt::Debug for Segment {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl core::fmt::Binary for Segment {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!("{:0>width$b}", &self.0, width = Segment::BITS))
    }
}
