use smallvec::SmallVec;

use super::BlackBox;

pub struct Benches;

type Shorts = SmallVec<[u16; 3]>;

impl<B: BlackBox> super::Benches<B> for Benches {
    fn from_exact_array_and_drop(&self, input: [u16; 3]) {
        let mut v = Shorts::from(input);
        B::black_box(&mut v);
        drop(v);
    }

    fn has_from_array_and_drop() -> bool { false }
    fn from_array_and_drop<const N: usize>(&self, _input: [u16; N]) { unimplemented!() }

    fn from_iter_and_drop(&self, input: impl Iterator<Item = u16>) {
        let mut v = Shorts::from_iter(input);
        B::black_box(&mut v);
        drop(v);
    }

    fn push_from_empty(&self, input: impl Iterator<Item = u16>) {
        let mut v = Shorts::default();

        for item in input {
            v.push(item);
            B::black_box(&mut v);
        }

        drop(v);
    }
}
