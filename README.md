# wordvec

[![GitHub CI](https://github.com/SOF3/wordvec/actions/workflows/ci.yml/badge.svg?event=push)](https://github.com/SOF3/wordvec/actions?query=workflow%3ACI)
[![crates.io](https://img.shields.io/crates/v/wordvec.svg)](https://crates.io/crates/wordvec)
[![crates.io](https://img.shields.io/crates/d/wordvec.svg)](https://crates.io/crates/wordvec)
[![docs.rs](https://docs.rs/wordvec/badge.svg)](https://docs.rs/wordvec)
[![GitHub](https://img.shields.io/github/last-commit/SOF3/wordvec)](https://github.com/SOF3/wordvec)
[![GitHub](https://img.shields.io/github/stars/SOF3/wordvec?style=social)](https://github.com/SOF3/wordvec)

A [thin][thinvec] and [small][smallvec] vector with memory footprint as small as a `usize`.

Specialized for large number of colocated small vectors,
such as `Vec<WordVec<T, N>>` or [ECS][ecs] components.

> This project has nothing to do with NLP embedding vectors.

## When to use

Use WordVec when all of the following meet your scenario:

### `N` is small

WordVec has no advantage over [SmallVec][smallvec] if it cannot pack into a smaller struct.
It is not meaningful to set `N` such that `align_of::<T>() + N * size_of::<T>()` exceeds 24.

### Length rarely exceeds `N`

When the length exceeds `N`, WordVec falls back to a thin heap allocation,
which is significantly (several times) slower than conventional vectors
because reading the length and capacity often results in CPU cache misses.

WordVec is ideally used when the expected behavior is
"length should never exceed `N`, but behavior is still correct when it exceeds".

### Many colocated vectors

Since the length encoding in the inlined layout is indirect (involves a bitshift),
raw inlined access also tends to be slower in WordVec compared to SmallVec,
as a tradeoff of reduced memory footprint of each vector alone.
However, it reduces the number of CPU cache misses due to tighter packing between inlined data,
which leads to better overall performance when many vectors are colocated.

This may get handy in scenarios with a large array of small vectors, e.g. [ECS][ecs],
where WordVec as a component would be packed in an archetype component storage contiguously.

### Iteration is more frequent than resizing

Resizing a WordVec involves bitshifting,
which may be more expensive than SmallVec/std::vec.
This tradeoff is only justified when
iteration is significantly more frequent than resizing.

## Memory layout

`WordVec<T, N>` has different layouts for small (inlined) and large (heap) lengths.
Inlined layout is used when the length is less than or equal to `N`,
while heap layout is used when the length exceeds `N`.
The type is a union of either inlined layout or heap layout.

### Inlined layout

WordVec can store up to `N` (generic const) items on the stack, where `N <= 127`:

```text
┌──────────┬────────────────────────┐
│ 1|len<<1 │   Elements (T × len)   │
└──────────┴────────────────────────┘
```

The length is stored in the 7 more significant bits of the first byte.
The least significant bit is always set.

If `T` has an alignment greater than 1,
there would be `align_of::<T>() - 1` padding bytes between the length and the first element.

### Heap layout

In the heap layout, WordVec is effectively a thin **pointer to** the following structure on the heap:

```text
┌────────┬──────────┬────────────────────────┐
│ length │ capacity │   Elements (T × cap)   │
└────────┴──────────┴────────────────────────┘
```

Since `length` and `capacity` are `usize`s,
the thin pointer is always a multiple of `align_of::<usize>()`.
Thus, the least significant bit of the thin pointer is always 0,
which distinguishes it from the inlined layout.

## Platform requirements

Targets violating the following requirements will lead to compile error:

- Little-endian only
- `align_of::<usize>()` must be at least 2 bytes.

## Benchmarks

Full criterion benchmark report generated from GitHub CI
can be found on [GitHub pages][bench-criterion].
Note that GitHub CI runners are subject to many uncontrolled noise sources
and may not be very reliable.
You may reproduce the benchmarks yourself by running `cargo bench --bench criterion`,
or check the [cachegrind analysis][bench-iai] instead.

The benchmarks compare `std::vec`, [`thinvec`][thinvec], [`smallvec`][smallvec] and `wordvec`.
The general observation is that WordVec performance is mostly comparable to SmallVec, but:

- WordVec is consistently slower with operations on a *single* small vector (presumably due to bitshifting the length byte),
  particularly resizing operations such as `push`.
- WordVec may be slower with operations on large vectors due to reading/writing length/capacity from heap.
- WordVec is consistently faster with iteration operations on *many* small vectors
  due to more efficient memory (fewer RAM accesses),
  particularly with operations updating the inner values of a `Vec<WordVec<T, N>>`.

[smallvec]: https://docs.rs/smallvec
[thinvec]: https://docs.rs/thin-vec
[std-vec]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[bench-criterion]: https://sof3.github.io/wordvec/report/index.html
[bench-iai]: https://sof3.github.io/wordvec/iai/summary.txt
[ecs]: https://en.wikipedia.org/wiki/Entity_component_system
