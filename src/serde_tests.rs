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
    test_deserialize_in_place::<5>(5, r#"["p", "q", "r", "s"]"#, 0, &["p", "q", "r", "s"], false);
}

#[test]
fn test_deserialize_in_place_large_grow_within_capacity() {
    test_deserialize_in_place::<2>(4, r#"["p", "q", "r", "s"]"#, 0, &["p", "q", "r", "s"], false);
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
    test_deserialize_in_place::<6>(6, r#"["p", "q", "r", "s", 3]"#, 0, &["p", "q", "r", "s"], true);
}

#[test]
fn test_deserialize_in_place_large_error_during_grow_within_capacity() {
    test_deserialize_in_place::<2>(6, r#"["p", "q", "r", "s", 3]"#, 0, &["p", "q", "r", "s"], true);
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
