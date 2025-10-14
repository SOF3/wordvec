use thin_vec::ThinVec;

use super::BlackBox;

#[allow(unused)]
pub struct Benches;

#[allow(unused)]
type Shorts = ThinVec<u16>;
#[allow(unused)]
type Words = ThinVec<usize>;

impl<B: BlackBox> super::Benches<B> for Benches {
    fn from_exact_array_and_drop(self, input: [u16; 3]) -> impl FnOnce() {
        move || {
            let mut v = Shorts::from(input);
            B::black_box(&mut v);
            drop(v);
        }
    }

    fn from_array_and_drop<const N: usize>(self, input: [u16; N]) -> impl FnOnce() {
        move || {
            let mut v = Shorts::from(input);
            B::black_box(&mut v);
            drop(v);
        }
    }

    fn from_iter_and_drop(self, input: impl Iterator<Item = u16>) -> impl FnOnce() {
        move || {
            let mut v = Shorts::from_iter(input);
            B::black_box(&mut v);
            drop(v);
        }
    }

    fn push_from_empty(self, input: impl Iterator<Item = u16>) -> impl FnOnce() {
        move || {
            let mut v = Shorts::default();

            for item in input {
                v.push(item);
                B::black_box(&mut v);
            }

            drop(v);
        }
    }

    fn remove_first(self, size: u16) -> impl FnOnce() {
        let mut v: Shorts = (0..size).collect();
        move || {
            B::black_box(v.remove(0));
            B::black_box(v);
        }
    }

    fn remove_second(self, size: u16) -> impl FnOnce() {
        let mut v: Shorts = (0..size).collect();
        move || {
            B::black_box(v.remove(1));
            B::black_box(v);
        }
    }

    fn inc_many_flat(self, each_size: u16, vec_count: usize) -> impl FnOnce() {
        let mut vecs: Vec<Shorts> = (0..vec_count)
            .map(|vec_index| {
                (0..each_size).map(|item_index| (vec_index as u16) ^ item_index).collect()
            })
            .collect();
        move || {
            for shorts in &mut vecs {
                shorts.iter_mut().for_each(|s| *s += 1);
            }
        }
    }

    fn inc_many_flat_pattern(self, pattern: &[u16], vec_count: usize) -> impl FnOnce() {
        let mut vecs: Vec<Shorts> = (0..vec_count)
            .flat_map(|pattern_index| {
                pattern.iter().copied().map(move |each_size| {
                    (0..each_size).map(|item_index| (pattern_index as u16) ^ item_index).collect()
                })
            })
            .collect();
        move || {
            for shorts in &mut vecs {
                shorts.iter_mut().for_each(|s| *s += 1);
            }
        }
    }

    fn index_many(
        self,
        buf_size: usize,
        indices: impl Iterator<Item = Vec<usize>>,
    ) -> impl FnOnce() {
        let mut buf = vec![0u64; buf_size];
        let mut vecs: Vec<Words> = indices.map(|v| v.into_iter().collect()).collect();
        B::black_box(&mut vecs);

        move || {
            for words in vecs {
                for index in words {
                    buf[index] = buf[index].wrapping_add(1);
                }
            }
            B::black_box(&mut buf);
        }
    }

    fn has_shrink_to() -> bool { false }
    fn shrink_to(self, _len: u16, _initial_cap: usize, _new_cap: usize) -> impl FnOnce() {
        move || unimplemented!()
    }

    fn shrink_to_fit(self, len: u16, initial_cap: usize) -> impl FnOnce() {
        let mut v: Shorts = Shorts::with_capacity(initial_cap);
        v.extend(0..len);

        move || {
            v.shrink_to_fit();
            B::black_box(&mut v);
        }
    }

    fn drain(self, len: u16, start: usize, end: usize) -> impl FnOnce() {
        let mut v: Shorts = (0..len).collect();

        move || {
            let drained = v.drain(start..end);
            for item in drained {
                B::black_box(item);
            }
            B::black_box(&mut v);
        }
    }
}
