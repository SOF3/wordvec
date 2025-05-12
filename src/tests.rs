use alloc::string::String;
use alloc::vec::Vec;

use crate::WordVec;

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
fn test_into_iter_drop() {
    fn assert<const N: usize>(inputs: &[&str], explicit_drops: usize) {
        let mut wv = WordVec::<String, N>::default();

        for &input in inputs {
            wv.push(input.into());
        }

        let mut iter = wv.into_iter();
        for _ in 0..explicit_drops {
            iter.next().unwrap();
        }

        drop(iter);
    }

    assert::<1>(&["a", "b", "c", "d"], 2);
}
