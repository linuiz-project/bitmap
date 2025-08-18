use core::num::NonZero;

use crate::{BitMap, Segment};

#[test]
fn segment_next_free_many() {
    let segment =
        Segment(0b00001111_11111111_11111111_11111111_11111111_11111111_11110001_00110111);
    // Safety: Value is non-zero.
    let bit_count = unsafe { NonZero::<u32>::new_unchecked(4) };
    assert_eq!(segment.next_free_many(bit_count), Some(60));

    // Safety: Value is non-zero.
    let bit_count = unsafe { NonZero::<u32>::new_unchecked(1) };
    let segment =
        Segment(0b01111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111);
    assert_eq!(segment.next_free_many(bit_count), Some(63));

    // Safety: Value is non-zero.
    let bit_count = unsafe { NonZero::<u32>::new_unchecked(1) };
    let segment = Segment(usize::MAX);
    assert_eq!(segment.next_free_many(bit_count), None);
}

#[test]
fn test() {
    unsafe {
        const SEGMENT_LEN: usize = 2;
        let memory = std::alloc::alloc(std::alloc::Layout::new::<[Segment; SEGMENT_LEN]>());
        let memory = std::slice::from_raw_parts_mut(memory.cast::<usize>(), SEGMENT_LEN);

        let mut bitmap = BitMap::new(memory, 128);

        bitmap.set(63..66).unwrap();
        println!("{bitmap:b}");
        assert_eq!(bitmap.segments, [Segment(0b1 << 63), Segment(0b11)]);
        bitmap.unset(64..65).unwrap();
        println!("{bitmap:b}");
        assert_eq!(bitmap.segments, [Segment(0b1 << 63), Segment(0b10)]);
    }
}
