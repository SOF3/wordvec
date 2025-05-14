use thin_vec::ThinVec;

use super::BlackBox;

pub struct Benches;

impl<B: BlackBox> super::Benches<B> for Benches {
    fn from_exact_array_and_drop(&self, input: [u16; 3]) {
        let mut v = ThinVec::from(input);
        B::black_box(&mut v);
        drop(v);
    }

    fn from_array_and_drop<const N: usize>(&self, input: [u16; N]) {
        let mut v = ThinVec::from(input);
        B::black_box(&mut v);
        drop(v);
    }

    fn from_iter_and_drop(&self, input: impl Iterator<Item = u16>) {
        let mut v = ThinVec::from_iter(input);
        B::black_box(&mut v);
        drop(v);
    }

    fn push_from_empty(&self, input: impl Iterator<Item = u16>) {
        let mut v = ThinVec::default();

        for item in input {
            v.push(item);
            B::black_box(&mut v);
        }

        drop(v);
    }
}
