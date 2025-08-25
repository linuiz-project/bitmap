use crate::{BitMap, Segment};
use core::num::NonZero;

#[test]
fn segment_next_free_many() {
    let mut segment =
        Segment::new(0b00001111_11111111_11111111_11111111_11111111_11111111_11110001_00110111);
    // Safety: Value is non-zero.
    let bit_count = unsafe { NonZero::<u32>::new_unchecked(4) };
    assert_eq!(segment.next_free(bit_count), Some(60));

    let mut segment =
        Segment::new(0b01111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111);
    assert_eq!(segment.next_free(NonZero::<u32>::MIN), Some(63));

    let mut segment = Segment::new(usize::MAX);
    assert_eq!(segment.next_free(NonZero::<u32>::MIN), None);
}

#[test]
fn test() {
    let mut memory = [0usize; 2];
    let mut bitmap = BitMap::new(&mut memory, 128);

    bitmap.set(63..66).unwrap();
    assert_eq!(
        bitmap.segments,
        [Segment::new(0b1 << 63), Segment::new(0b11)]
    );
    bitmap.unset(64..65).unwrap();
    assert_eq!(
        bitmap.segments,
        [Segment::new(0b1 << 63), Segment::new(0b10)]
    );
}

#[test]
fn bitmap_inbetween() {
    let mut memory = [0usize; 3];
    let bit_length = Segment::BITS * memory.len();
    let mut bitmap = BitMap::new(&mut memory, bit_length);
    bitmap.set(..63).unwrap();
    bitmap.set(130..).unwrap();
    assert_eq!(bitmap, &[0x7FFF_FFFF_FFFF_FFFF, 0x0, 0xFFFF_FFFF_FFFF_FFFC]);

    // Safety: Value is non-zero.
    let next_free_size = unsafe { NonZero::<usize>::new_unchecked(66) };
    bitmap.next_free(next_free_size);
    assert_eq!(
        bitmap,
        &[
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFD
        ]
    );
}
