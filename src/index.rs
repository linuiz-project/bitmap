use crate::{
    BitMap, BitMapError, bitmap_get_bit, bitmap_get_bits, bitmap_set_bit, bitmap_set_bits,
};

pub trait BitMapIndex {
    fn get(&self, bitmap: &BitMap) -> Result<bool, BitMapError>;

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError>;
    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError>;
}

impl BitMapIndex for usize {
    fn get(&self, bitmap: &BitMap) -> Result<bool, BitMapError> {
        bitmap_get_bit(*self, bitmap)
    }

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bit(*self, bitmap, true)
    }

    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bit(*self, bitmap, false)
    }
}

impl BitMapIndex for core::ops::Range<usize> {
    fn get(&self, bitmap: &BitMap) -> Result<bool, BitMapError> {
        bitmap_get_bits(self.start, self.end, bitmap)
    }

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(self.start, self.end, bitmap, true)
    }

    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(self.start, self.end, bitmap, false)
    }
}

impl BitMapIndex for core::ops::RangeTo<usize> {
    fn get(&self, bitmap: &BitMap) -> Result<bool, BitMapError> {
        bitmap_get_bits(0, self.end, bitmap)
    }

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(0, self.end, bitmap, true)
    }

    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(0, self.end, bitmap, false)
    }
}

impl BitMapIndex for core::ops::RangeFrom<usize> {
    fn get(&self, bitmap: &BitMap) -> Result<bool, BitMapError> {
        bitmap_get_bits(self.start, bitmap.bit_len, bitmap)
    }

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(self.start, bitmap.bit_len, bitmap, true)
    }

    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(self.start, bitmap.bit_len, bitmap, false)
    }
}

impl BitMapIndex for core::ops::RangeFull {
    fn get(&self, bitmap: &BitMap) -> Result<bool, BitMapError> {
        bitmap_get_bits(0, bitmap.bit_len, bitmap)
    }

    fn set(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(0, bitmap.bit_len, bitmap, true)
    }

    fn unset(&self, bitmap: &mut BitMap) -> Result<(), BitMapError> {
        bitmap_set_bits(0, bitmap.bit_len, bitmap, false)
    }
}
