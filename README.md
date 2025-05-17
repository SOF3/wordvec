# wordvec

[![GitHub CI](https://github.com/SOF3/wordvec/workflows/CI/badge.svg)](https://github.com/SOF3/wordvec/actions?query=workflow%3ACI)
[![crates.io](https://img.shields.io/crates/v/wordvec.svg)](https://crates.io/crates/wordvec)
[![crates.io](https://img.shields.io/crates/d/wordvec.svg)](https://crates.io/crates/wordvec)
[![docs.rs](https://docs.rs/wordvec/badge.svg)](https://docs.rs/wordvec)
[![GitHub](https://img.shields.io/github/last-commit/SOF3/wordvec)](https://github.com/SOF3/wordvec)
[![GitHub](https://img.shields.io/github/stars/SOF3/wordvec?style=social)](https://github.com/SOF3/wordvec)

A [thin][thinvec] and [small][smallvec] vector
that can fit data into a single `usize`.

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

## When to use

Although the technical limit is `N <= 127`,
it is not meaningful to set `N` such that `align_of::<T>() + N * size_of::<T>()` exceeds 24;
WordVec has no advantage over [SmallVec][smallvec] if it cannot pack into a smaller struct.

Thin vectors are significantly (several times) slower than conventional vectors
since reading the length and capacity usually involves accessing memory out of active cache.
Thus, heap layout is supposed to be the cold path.
In other words, WordVec is basically
"length should never exceed `N`, but behavior is still correct when it exceeds".

Since the length encoding in the inlined layout is indirect (involves a bitshift),
raw inlined access also tends to be slower in WordVec compared to SmallVec,
as a tradeoff of reduced memory footprint of each vector alone.
This may get handy in scenarios with a large array of small vectors,
e.g. as an ECS component.

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
or check the [valgrind-based analysis][bench-iai] instead.

The benchmarks compare `std::vec`, 

The general observation is that WordVec performance is comparable to SmallVec, but:
- is slower with operations on a *single* small vector (presumably due to bitshifting the length byte)
- is sometimes slower with operations on large vectors due to thinness (reading/writing length/capacity from heap)
- is sometimes faster with operations on *many* small vectors due to more efficient memory (fewer RAM accesses)

## Vec feature parity

WordVec is a new project to experiment on new semantics.
Currently only the basic features required to produce meaningful benchmarks are implemented,
but **all features from `std::vec` shall be implemented** in this library eventually.
Pull requests are welcome to align WordVec functionality with `std::vec` or smallvec;
I do not have bandwidth to implement all those functions but I am happy to review such contributions.

[smallvec]: https://docs.rs/smallvec
[thinvec]: https://docs.rs/thin-vec
[std-vec]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[bench-criterion]: https://sof3.github.io/wordvec/report/index.html
[bench-iai]: https://sof3.github.io/wordvec/iai/summary.txt
