use super::BlackBox;

pub struct Benches;

impl<B: BlackBox> super::Benches<B> for Benches {
    fn from_exact_array_and_drop(self, input: [u16; 3]) -> impl FnOnce() {
        move || {
            let mut v = Vec::from(input);
            B::black_box(&mut v);
            drop(v);
        }
    }

    fn from_array_and_drop<const N: usize>(self, input: [u16; N]) -> impl FnOnce() {
        move || {
            let mut v = Vec::from(input);
            B::black_box(&mut v);
            drop(v);
        }
    }

    fn from_iter_and_drop(self, input: impl Iterator<Item = u16>) -> impl FnOnce() {
        move || {
            let mut v = Vec::from_iter(input);
            B::black_box(&mut v);
            drop(v);
        }
    }

    fn push_from_empty(self, input: impl Iterator<Item = u16>) -> impl FnOnce() {
        move || {
            let mut v = Vec::default();

            for item in input {
                v.push(item);
                B::black_box(&mut v);
            }

            drop(v);
        }
    }

    fn remove_first(self, size: u16) -> impl FnOnce() {
        let mut v: Vec<_> = (0..size).collect();
        move || {
            B::black_box(v.remove(0));
            B::black_box(v);
        }
    }

    fn remove_second(self, size: u16) -> impl FnOnce() {
        let mut v: Vec<_> = (0..size).collect();
        move || {
            B::black_box(v.remove(1));
            B::black_box(v);
        }
    }
}
