use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cell::Cell;

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
fn test_drain_long_short_long() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..5).collect();
    assert_eq!(drained, [3, 4]);
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
fn test_drain_long_long_short() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..6).collect();
    assert_eq!(drained, [3, 4, 5]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 6, 7]);
}

#[test]
fn test_drain_long_long_short_early_drop() {
    let mut wv = (0..8).collect::<WordVec<_, 10>>();
    let drained: Vec<_> = wv.drain(3..6).take(1).collect();
    assert_eq!(drained, [3]);
    assert_eq!(wv.as_slice(), &[0, 1, 2, 6, 7]);
}

#[cfg(feature = "serde")]
mod test_serde {
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::cell::Cell;

    use serde::Deserialize;
    use serde_json::json;

    use crate::WordVec;

    struct AssertInPlace<'a> {
        value:        String,
        in_place:     bool,
        drop_counter: Option<&'a Cell<usize>>,
    }

    impl<'de> Deserialize<'de> for AssertInPlace<'_> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            Ok(Self {
                value:        String::deserialize(deserializer)?,
                in_place:     false,
                drop_counter: None,
            })
        }

        fn deserialize_in_place<D>(deserializer: D, place: &mut Self) -> Result<(), D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            String::deserialize_in_place(deserializer, &mut place.value)?;
            place.in_place = true;
            Ok(())
        }
    }

    impl Drop for AssertInPlace<'_> {
        fn drop(&mut self) {
            let counter = self
                .drop_counter
                .expect("AssertInPlace dropped without having set a drop_counter first");
            counter.set(counter.get() + 1);
        }
    }

    #[test]
    fn test_serialize_small() {
        let source = WordVec::<_, 4>::from(["a", "b", "c"]);
        let value = serde_json::to_value(&source).unwrap();
        assert_eq!(value, json!(["a", "b", "c"]));
    }

    #[test]
    fn test_serialize_large() {
        let source = WordVec::<_, 2>::from(["a", "b", "c"]);
        let value = serde_json::to_value(&source).unwrap();
        assert_eq!(value, json!(["a", "b", "c"]));
    }

    #[test]
    fn test_deserialize_small() {
        let value: WordVec<String, 4> = serde_json::from_str(r#"["a", "b", "c"]"#).unwrap();
        assert_eq!(value.as_slice(), &["a", "b", "c"]);
    }

    #[test]
    fn test_deserialize_large() {
        let value: WordVec<String, 2> = serde_json::from_str(r#"["a", "b", "c"]"#).unwrap();
        assert_eq!(value.as_slice(), &["a", "b", "c"]);
    }

    fn test_deserialize_in_place<const N: usize>(
        initial_capacity: usize,
        input: &str,
        expect_drops_during_de: usize,
        expect_data: &[&str],
        expect_err: bool,
    ) {
        let drop_counter = Cell::new(0);
        let mut wv: WordVec<AssertInPlace, N> = WordVec::with_capacity(initial_capacity);
        for s in ["a", "b", "c"] {
            wv.push(AssertInPlace {
                value:        s.into(),
                in_place:     false,
                drop_counter: Some(&drop_counter),
            });
        }

        let result =
            WordVec::deserialize_in_place(&mut serde_json::Deserializer::from_str(input), &mut wv);
        assert_eq!(result.is_err(), expect_err);

        let drops_during_de = drop_counter.get();
        assert_eq!(drops_during_de, expect_drops_during_de);

        assert_eq!(wv.as_slice().iter().map(|s| s.value.as_str()).collect::<Vec<_>>(), expect_data);

        for (index, item) in wv.iter().take(3).enumerate() {
            assert!(item.in_place, "item #{index} should be deserialized in place");
        }

        for item in wv.iter_mut().skip(3) {
            item.drop_counter = Some(&drop_counter);
        }

        drop(wv); // ensure drops_during_de is fetched before dropping `value`.
        assert_eq!(drop_counter.get(), expect_drops_during_de + expect_data.len());
    }

    #[test]
    fn test_deserialize_in_place_small_shrink() {
        test_deserialize_in_place::<4>(4, r#"["p", "q"]"#, 1, &["p", "q"], false);
    }

    #[test]
    fn test_deserialize_in_place_large_shrink() {
        test_deserialize_in_place::<2>(4, r#"["p", "q"]"#, 1, &["p", "q"], false);
    }

    #[test]
    fn test_deserialize_in_place_small_grow_within_capacity() {
        test_deserialize_in_place::<5>(
            5,
            r#"["p", "q", "r", "s"]"#,
            0,
            &["p", "q", "r", "s"],
            false,
        );
    }

    #[test]
    fn test_deserialize_in_place_large_grow_within_capacity() {
        test_deserialize_in_place::<2>(
            4,
            r#"["p", "q", "r", "s"]"#,
            0,
            &["p", "q", "r", "s"],
            false,
        );
    }

    #[test]
    fn test_deserialize_in_place_small_grow_to_large() {
        test_deserialize_in_place::<4>(
            4,
            r#"["p", "q", "r", "s", "t"]"#,
            0,
            &["p", "q", "r", "s", "t"],
            false,
        );
    }

    #[test]
    fn test_deserialize_in_place_large_grow() {
        test_deserialize_in_place::<2>(
            4,
            r#"["p", "q", "r", "s", "t"]"#,
            0,
            &["p", "q", "r", "s", "t"],
            false,
        );
    }

    #[test]
    fn test_deserialize_in_place_small_error_causing_shrink() {
        test_deserialize_in_place::<4>(4, r#"["p", "q", 3]"#, 1, &["p", "q"], true);
    }

    #[test]
    fn test_deserialize_in_place_large_error_causing_shrink() {
        test_deserialize_in_place::<2>(4, r#"["p", "q", 3]"#, 1, &["p", "q"], true);
    }

    #[test]
    fn test_deserialize_in_place_small_error_during_grow_within_capacity() {
        test_deserialize_in_place::<6>(
            6,
            r#"["p", "q", "r", "s", 3]"#,
            0,
            &["p", "q", "r", "s"],
            true,
        );
    }

    #[test]
    fn test_deserialize_in_place_large_error_during_grow_within_capacity() {
        test_deserialize_in_place::<2>(
            6,
            r#"["p", "q", "r", "s", 3]"#,
            0,
            &["p", "q", "r", "s"],
            true,
        );
    }

    #[test]
    fn test_deserialize_in_place_large_error_during_grow_beyond_capacity() {
        test_deserialize_in_place::<2>(
            4,
            r#"["p", "q", "r", "s", "t", "u", 3]"#,
            0,
            &["p", "q", "r", "s", "t", "u"],
            true,
        );
    }
}
