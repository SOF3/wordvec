use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cell::Cell;
use core::panic::AssertUnwindSafe;

use crate::WordVec;

#[test]
#[cfg(target_pointer_width = "64")]
fn assert_size() {
    assert_eq!(size_of::<WordVec<i32, 1>>(), 8);
    assert_eq!(size_of::<WordVec<i16, 3>>(), 8);
    assert_eq!(size_of::<WordVec<i8, 7>>(), 8);
}

struct AssertDrop<'a> {
    string:  String,
    counter: &'a Cell<usize>,
}

impl Drop for AssertDrop<'_> {
    fn drop(&mut self) { self.counter.set(self.counter.get() + 1); }
}

#[test]
fn test_from_and_as_slice() {
    fn assert<const N: usize, const M: usize>(inputs: [i32; M]) {
        let wv = WordVec::<i32, N>::from(inputs);
        assert_eq!(wv.as_slice(), &inputs[..]);
    }

    assert::<1, 0>([]);
    assert::<1, 1>([42]);
    assert::<1, 2>([42, 55]);
    assert::<2, 0>([]);
    assert::<2, 1>([42]);
    assert::<2, 2>([42, 55]);
}

#[test]
fn test_new_inlined() {
    fn assert<const N: usize, const M: usize>(inputs: [i32; M]) {
        let wv = WordVec::<i32, N>::new_inlined(inputs);
        assert_eq!(wv.as_slice(), &inputs[..]);
    }

    assert::<1, 0>([]);
    assert::<1, 1>([42]);
    assert::<2, 0>([]);
    assert::<2, 1>([42]);
    assert::<2, 2>([42, 55]);
}

#[test]
fn test_with_capacity() {
    assert_eq!(WordVec::<i32, 2>::with_capacity(0).capacity(), 2);
    assert_eq!(WordVec::<i32, 2>::with_capacity(1).capacity(), 2);
    assert_eq!(WordVec::<i32, 2>::with_capacity(2).capacity(), 2);
    assert_eq!(WordVec::<i32, 2>::with_capacity(3).capacity(), 3);

    let mut wv = WordVec::<i32, 2>::with_capacity(3);

    wv.push(11);
    assert_eq!(wv.len(), 1);
    assert_eq!(wv.capacity(), 3);

    wv.push(12);
    assert_eq!(wv.len(), 2);
    assert_eq!(wv.capacity(), 3);

    wv.push(13);
    assert_eq!(wv.len(), 3);
    assert_eq!(wv.capacity(), 3);

    wv.push(14);
    assert_eq!(wv.len(), 4);
    assert_eq!(wv.capacity(), 6);
}

#[test]
fn test_push() {
    let mut wv = WordVec::<i32, 2>::new();
    wv.push(42);
    assert_eq!(wv.len(), 1);
    assert_eq!(wv.as_slice(), &[42]);
    wv.push(55);
    assert_eq!(wv.len(), 2);
    assert_eq!(wv.as_slice(), &[42, 55]);
    wv.push(67);
    assert_eq!(wv.len(), 3);
    assert_eq!(wv.as_slice(), &[42, 55, 67]);
    wv.push(93);
    assert_eq!(wv.len(), 4);
    assert_eq!(wv.as_slice(), &[42, 55, 67, 93]);
    wv.push(24);
    assert_eq!(wv.len(), 5);
    assert_eq!(wv.as_slice(), &[42, 55, 67, 93, 24]);
}

#[test]
fn test_extend() {
    let mut wv = WordVec::<i32, 2>::new();
    wv.extend([42]);
    assert_eq!(wv.len(), 1);
    assert_eq!(wv.as_slice(), &[42]);
    wv.extend([55, 67]);
    assert_eq!(wv.len(), 3);
    assert_eq!(wv.as_slice(), &[42, 55, 67]);
    wv.extend([93, 24, 17, 84]);
    assert_eq!(wv.len(), 7);
    assert_eq!(wv.as_slice(), &[42, 55, 67, 93, 24, 17, 84]);
}

#[test]
fn test_from_and_into_iter() {
    fn assert<const N: usize, const M: usize>(inputs: [i32; M]) {
        let wv = WordVec::<i32, N>::from(inputs);
        let vec: Vec<_> = wv.into_iter().collect();
        assert_eq!(vec, inputs);
    }

    assert::<1, 0>([]);
    assert::<1, 1>([42]);
    assert::<1, 2>([42, 55]);
    assert::<2, 0>([]);
    assert::<2, 1>([42]);
    assert::<2, 2>([42, 55]);
}

#[test]
fn test_from_iter_and_into_iter() {
    fn assert<const N: usize>(inputs: impl IntoIterator<Item = i32> + Clone) {
        let wv = WordVec::<i32, N>::from_iter(inputs.clone());
        let vec: Vec<_> = wv.into_iter().collect();
        assert_eq!(vec, inputs.into_iter().collect::<Vec<_>>());
    }

    assert::<1>([]);
    assert::<1>([42]);
    assert::<1>([42, 55]);
    assert::<2>([]);
    assert::<2>([42]);
    assert::<2>([42, 55]);
    assert::<2>([42, 55, 66, 88, 47, 92, 85, 23, 51]);
}

#[test]
fn test_from_iter_string_and_into_iter() {
    fn assert<const N: usize>(inputs: impl IntoIterator<Item = i32, IntoIter: Clone>) {
        let inputs = inputs.into_iter().map(|i| i.to_string());

        #[expect(clippy::from_iter_instead_of_collect)] // for explicitness
        let wv = WordVec::<String, N>::from_iter(inputs.clone());
        let vec: Vec<_> = wv.into_iter().collect();
        assert_eq!(vec, inputs.into_iter().collect::<Vec<_>>());
    }

    assert::<1>([]);
    assert::<1>([42]);
    assert::<1>([42, 55]);
    assert::<2>([]);
    assert::<2>([42]);
    assert::<2>([42, 55]);
    assert::<2>([42, 55, 66, 88, 47, 92, 85, 23, 51]);
}

#[test]
fn test_into_iter_drop() {
    fn assert<const N: usize>(inputs: &[&str], explicit_drops: usize) {
        let counter = Cell::new(0);

        let mut wv = WordVec::<AssertDrop, N>::default();

        for &input in inputs {
            wv.push(AssertDrop { string: input.into(), counter: &counter });
        }

        assert_eq!(counter.get(), 0);

        let mut iter = wv.into_iter();
        assert_eq!(counter.get(), 0);

        for _ in 0..explicit_drops {
            iter.next().unwrap();
        }
        assert_eq!(counter.get(), explicit_drops);

        drop(iter);
        assert_eq!(counter.get(), inputs.len());
    }

    assert::<8>(&["a", "b", "c", "d", "e"], 0);
    assert::<8>(&["a", "b", "c", "d", "e"], 2);
    assert::<1>(&["a", "b", "c", "d", "e"], 0);
    assert::<1>(&["a", "b", "c", "d", "e"], 2);
    assert::<1>(&["a", "b", "c", "d", "e"], 3);
}

#[test]
fn test_remove_small() {
    let mut wv = WordVec::<i32, 4>::from([1, 2, 3]);
    assert_eq!(wv.remove(0), 1);
    assert_eq!(wv.as_slice(), &[2, 3]);

    assert!(wv.try_remove(2).is_none());
}

#[test]
fn test_remove_large() {
    let mut wv = WordVec::<i32, 4>::from([1, 2, 3, 4, 5]);
    assert_eq!(wv.remove(0), 1);
    assert_eq!(wv.as_slice(), &[2, 3, 4, 5]);
    assert_eq!(wv.remove(1), 3);
    assert_eq!(wv.as_slice(), &[2, 4, 5]);

    assert!(wv.try_remove(3).is_none());
}

#[test]
fn test_swap_remove_small() {
    let mut wv = WordVec::<i32, 4>::from([1, 2, 3]);
    assert_eq!(wv.swap_remove(0), 1);
    assert_eq!(wv.as_slice(), &[3, 2]);

    assert!(wv.try_swap_remove(2).is_none());
}

#[test]
fn test_swap_remove_large() {
    let mut wv = WordVec::<i32, 4>::from([1, 2, 3, 4, 5]);
    assert_eq!(wv.swap_remove(0), 1);
    assert_eq!(wv.as_slice(), &[5, 2, 3, 4]);
    assert_eq!(wv.swap_remove(1), 2);
    assert_eq!(wv.as_slice(), &[5, 4, 3]);

    assert!(wv.try_swap_remove(3).is_none());
}

#[test]
fn test_pop_empty() {
    let mut wv = WordVec::<i32, 4>::new();
    assert!(wv.pop().is_none());
    assert!(wv.as_slice().is_empty());
}

#[test]
fn test_pop_small() {
    let mut wv = WordVec::<i32, 4>::from([1, 2]);
    assert_eq!(wv.pop(), Some(2));
    assert_eq!(wv.as_slice(), &[1]);
}

#[test]
fn test_pop_large() {
    let mut wv = WordVec::<i32, 2>::from([1, 2, 3, 4]);

    assert_eq!(wv.pop(), Some(4));
    assert_eq!(wv.as_slice(), &[1, 2, 3]);

    assert_eq!(wv.pop(), Some(3));
    assert_eq!(wv.as_slice(), &[1, 2]);

    assert_eq!(wv.pop(), Some(2));
    assert_eq!(wv.as_slice(), &[1]);

    assert_eq!(wv.pop(), Some(1));
    assert!(wv.as_slice().is_empty());

    assert!(wv.pop().is_none());
    assert!(wv.as_slice().is_empty());
}

#[test]
fn test_clear() {
    fn assert<const N: usize>(input: &[&str], cap: usize) {
        let counter = Cell::new(0);
        let mut wv = WordVec::<AssertDrop, N>::with_capacity(cap);
        wv.extend(input.iter().map(|&s| AssertDrop { string: s.into(), counter: &counter }));

        assert_eq!(wv.len(), input.len());
        assert_eq!(wv.capacity(), cap);
        assert_eq!(counter.get(), 0);

        wv.clear();

        assert_eq!(wv.len(), 0);
        assert_eq!(wv.capacity(), cap);
        assert_eq!(counter.get(), input.len());
    }

    assert::<4>(&["a", "b", "c"], 4);
    assert::<2>(&["a", "b", "c"], 4);
}

#[test]
fn test_shrink() {
    fn assert<const N: usize>(
        input: &[&str],
        initial_cap: usize,
        shrink_to: usize,
        expected_cap: usize,
    ) {
        let counter = Cell::new(0);
        let mut wv = WordVec::<AssertDrop, N>::with_capacity(initial_cap);
        wv.extend(input.iter().map(|&s| AssertDrop { string: s.into(), counter: &counter }));

        assert_eq!(wv.len(), input.len());
        assert_eq!(wv.capacity(), initial_cap);
        assert_eq!(counter.get(), 0);

        wv.shrink_to(shrink_to);

        assert_eq!(wv.len(), input.len());
        assert_eq!(wv.capacity(), expected_cap);
        assert_eq!(counter.get(), 0);

        drop(wv);

        assert_eq!(counter.get(), input.len());
    }

    assert::<2>(&["a", "b", "c"], 8, 4, 4);
    assert::<2>(&["a", "b", "c"], 8, 2, 3);
    assert::<4>(&["a", "b", "c"], 8, 2, 4);
    assert::<4>(&["a", "b", "c"], 8, 5, 5);
}

#[test]
fn test_reserve() {
    fn assert<const N: usize>(
        input: &[&str],
        initial_cap: usize,
        additional: usize,
        expect_cap: usize,
    ) {
        let counter = Cell::new(0);
        let mut wv = WordVec::<AssertDrop, N>::with_capacity(initial_cap);
        wv.extend(input.iter().map(|&s| AssertDrop { string: s.into(), counter: &counter }));

        assert_eq!(wv.len(), input.len());
        assert_eq!(wv.capacity(), initial_cap);
        assert_eq!(counter.get(), 0);

        wv.reserve(additional);

        assert_eq!(wv.as_slice().len(), input.len());
        assert_eq!(wv.capacity(), expect_cap);
        assert_eq!(counter.get(), 0);

        drop(wv);

        assert_eq!(counter.get(), input.len());
    }

    assert::<4>(&["a", "b"], 4, 1, 4);
    assert::<4>(&["a", "b"], 4, 3, 8);
    assert::<2>(&["a", "b", "c"], 4, 1, 4);
    assert::<2>(&["a", "b", "c"], 4, 3, 8);
}

#[test]
fn test_reserve_exact() {
    fn assert<const N: usize>(
        input: &[&str],
        initial_cap: usize,
        additional: usize,
        expect_cap: usize,
    ) {
        let counter = Cell::new(0);
        let mut wv = WordVec::<AssertDrop, N>::with_capacity(initial_cap);
        wv.extend(input.iter().map(|&s| AssertDrop { string: s.into(), counter: &counter }));

        assert_eq!(wv.len(), input.len());
        assert_eq!(wv.capacity(), initial_cap);
        assert_eq!(counter.get(), 0);

        wv.reserve_exact(additional);

        assert_eq!(wv.as_slice().len(), input.len());
        assert_eq!(wv.capacity(), expect_cap);
        assert_eq!(counter.get(), 0);

        drop(wv);

        assert_eq!(counter.get(), input.len());
    }

    assert::<4>(&["a", "b"], 4, 1, 4);
    assert::<4>(&["a", "b"], 4, 3, 5);
    assert::<2>(&["a", "b", "c"], 4, 1, 4);
    assert::<2>(&["a", "b", "c"], 4, 3, 6);
}

#[test]
fn test_insert() {
    fn assert<const N: usize>(input: &[&str], index: usize, val: &str, expect: &[&str]) {
        let counter = Cell::new(0);
        let mut wv: WordVec<AssertDrop, N> =
            input.iter().map(|&s| AssertDrop { string: s.into(), counter: &counter }).collect();
        wv.insert(index, AssertDrop { string: val.into(), counter: &counter });
        assert_eq!(wv.as_slice().iter().map(|s| s.string.as_str()).collect::<Vec<_>>(), expect);
        assert_eq!(counter.get(), 0);

        drop(wv);
        assert_eq!(counter.get(), expect.len());
    }

    assert::<4>(&[], 0, "a", &["a"]);
    assert::<0>(&[], 0, "a", &["a"]);

    assert::<4>(&["a", "b"], 0, "c", &["c", "a", "b"]);
    assert::<3>(&["a", "b"], 0, "c", &["c", "a", "b"]);
    assert::<2>(&["a", "b"], 0, "c", &["c", "a", "b"]);
    assert::<1>(&["a", "b"], 0, "c", &["c", "a", "b"]);

    assert::<4>(&["a", "b"], 1, "c", &["a", "c", "b"]);
    assert::<3>(&["a", "b"], 1, "c", &["a", "c", "b"]);
    assert::<2>(&["a", "b"], 1, "c", &["a", "c", "b"]);
    assert::<1>(&["a", "b"], 1, "c", &["a", "c", "b"]);

    assert::<4>(&["a", "b"], 2, "c", &["a", "b", "c"]);
    assert::<3>(&["a", "b"], 2, "c", &["a", "b", "c"]);
    assert::<2>(&["a", "b"], 2, "c", &["a", "b", "c"]);
    assert::<1>(&["a", "b"], 2, "c", &["a", "b", "c"]);
}

#[test]
fn test_drain_nothing() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..3).collect();
    assert!(drained.is_empty());
    assert_eq!(wv.as_slice(), &[0, 1, 2, 3, 4, 5, 6, 7]);
}

#[test]
fn test_drain_everything() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(0..8).collect();
    assert_eq!(drained, [0, 1, 2, 3, 4, 5, 6, 7]);
    assert!(wv.as_slice().is_empty());
}

#[test]
fn test_drain_drop_calls_destructor() {
    let counter = &Cell::new(0);
    let mut wv =
        (0..8).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 10>>();
    drop(wv.drain(3..5));
    assert_eq!(counter.get(), 2);
    drop(wv); // ensure wv is dropped after counter check
}

#[test]
fn test_drain_len_calls_destructor() {
    let counter = &Cell::new(0);
    let mut wv =
        (0..8).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 10>>();
    assert_eq!(wv.drain(3..5).len(), 2);
    assert_eq!(counter.get(), 2);
    drop(wv); // ensure wv is dropped after counter check
}

#[test]
fn test_drain_len_trimmed_calls_destructor() {
    let counter = &Cell::new(0);
    let mut wv =
        (0..8).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 10>>();
    let mut drain = wv.drain(3..6);
    assert_eq!(drain.next().map(|v| v.string.clone()), Some("3".into()));
    assert_eq!(drain.next_back().map(|v| v.string.clone()), Some("5".into()));
    assert_eq!(drain.len(), 1);
    assert_eq!(counter.get(), 2);
    assert_eq!(drain.count(), 1);
    assert_eq!(counter.get(), 3);
    drop(wv); // ensure wv is dropped after counter check
    assert_eq!(counter.get(), 8);
}

#[test]
fn test_drain_long_short_long() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..5).collect();
    assert_eq!(drained, [3, 4]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 5, 6, 7]);
}

#[test]
fn test_drain_long_short_long_back() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..5).rev().collect();
    assert_eq!(drained, [4, 3]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 5, 6, 7]);
}

#[test]
fn test_drain_long_short_long_early_drop() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..5).take(1).collect();
    assert_eq!(drained, [3]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 5, 6, 7]);
}

#[test]
fn test_drain_long_short_long_early_drop_back() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..5).rev().take(1).collect();
    assert_eq!(drained, [4]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 5, 6, 7]);
}

#[test]
fn test_drain_long_long_short() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..6).collect();
    assert_eq!(drained, [3, 4, 5]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 6, 7]);
}

#[test]
fn test_drain_long_long_short_back() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..6).rev().collect();
    assert_eq!(drained, [5, 4, 3]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 6, 7]);
}

#[test]
fn test_drain_long_long_short_early_drop() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..6).take(1).collect();
    assert_eq!(drained, [3]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 6, 7]);
}

#[test]
fn test_drain_long_long_short_early_drop_back() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..6).rev().take(1).collect();
    assert_eq!(drained, [5]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 6, 7]);
}

#[test]
fn test_retain_empty() {
    let mut wv = WordVec::<i32, 4>::new();
    wv.retain(|_| unreachable!());
    assert!(wv.as_slice().is_empty());
}

#[test]
fn test_retain_everything() {
    let counter = &Cell::new(0);
    let mut wv =
        (0..3).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 4>>();
    wv.retain(|_| true);
    assert_eq!(counter.get(), 0);
    assert_eq!(wv.iter().map(|d| d.string.as_str()).collect::<Vec<_>>(), &["0", "1", "2"]);
    drop(wv);
    assert_eq!(counter.get(), 3);
}

#[test]
fn test_retain_nothing() {
    let counter = &Cell::new(0);
    let mut wv =
        (0..3).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 4>>();
    wv.retain(|_| false);
    assert_eq!(counter.get(), 3);
    assert!(wv.as_slice().is_empty());
}

#[test]
fn test_retain_tft() {
    let counter = &Cell::new(0);
    let mut wv =
        (0..3).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 4>>();
    let mut retain_seq = [true, false, true].into_iter();
    wv.retain(|_| retain_seq.next().unwrap());
    assert_eq!(counter.get(), 1);
    assert_eq!(wv.iter().map(|d| d.string.as_str()).collect::<Vec<_>>(), &["0", "2"]);
    drop(wv);
    assert_eq!(counter.get(), 3);
}

#[test]
fn test_retain_ftf() {
    let counter = &Cell::new(0);
    let mut wv =
        (0..3).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 4>>();
    let mut retain_seq = [false, true, false].into_iter();
    wv.retain(|_| retain_seq.next().unwrap());
    assert_eq!(counter.get(), 2);
    assert_eq!(wv.iter().map(|d| d.string.as_str()).collect::<Vec<_>>(), &["1"]);
    drop(wv);
    assert_eq!(counter.get(), 3);
}

fn test_retain_panic(retain_prev: bool, expect_retain_drops: usize, expect_after_retain: &[&str]) {
    extern crate std;

    let counter = &Cell::new(0);
    let mut wv =
        (0..3).map(|i| AssertDrop { string: i.to_string(), counter }).collect::<WordVec<_, 4>>();

    _ = std::panic::catch_unwind({
        let mut wv = AssertUnwindSafe(&mut wv);
        move || {
            let mut next_index = 0;
            wv.retain(|_| {
                let index = next_index;
                next_index += 1;

                #[expect(clippy::manual_assert, reason = "clarity")]
                if index == 1 {
                    panic!("intentional panic");
                }

                retain_prev
            });
        }
    });

    assert_eq!(counter.get(), expect_retain_drops);
    assert_eq!(wv.iter().map(|d| d.string.as_str()).collect::<Vec<_>>(), expect_after_retain);
    drop(wv);
    assert_eq!(counter.get(), 3);
}

#[test]
fn test_retain_shifted_panic() { test_retain_panic(false, 1, &["1", "2"]); }

#[test]
fn test_retain_unshifted_panic() { test_retain_panic(true, 0, &["0", "1", "2"]); }

fn assert_resize<const N: usize>(
    initial_len: usize,
    resize_len: usize,
    expect_slice: &[i32],
    expect_resize_drops: usize,
) {
    let counter = &Cell::new(0);
    let mut wv = (0..initial_len)
        .map(|i| AssertDrop { string: i.to_string(), counter })
        .collect::<WordVec<_, N>>();
    wv.resize_with(resize_len, || AssertDrop { string: "9".to_string(), counter });
    assert_eq!(
        wv.as_slice().iter().map(|d| d.string.parse::<i32>().unwrap()).collect::<Vec<_>>(),
        expect_slice
    );
    assert_eq!(counter.get(), expect_resize_drops);
    drop(wv);
    assert_eq!(counter.get(), initial_len.max(resize_len));
}

#[test]
fn test_resize_unchanged() { assert_resize::<5>(4, 4, &[0, 1, 2, 3], 0); }

#[test]
fn test_resize_truncate() { assert_resize::<5>(4, 2, &[0, 1], 2); }

#[test]
fn test_resize_extend_in_place() { assert_resize::<5>(2, 5, &[0, 1, 9, 9, 9], 0); }

#[test]
fn test_resize_extend_grow_small() { assert_resize::<4>(2, 5, &[0, 1, 9, 9, 9], 0); }

#[test]
fn test_resize_extend_grow_large() { assert_resize::<1>(2, 5, &[0, 1, 9, 9, 9], 0); }
