# wordvec

A compact `SmallVec<T>`-like container with only `align_of::<T>()` overhead for small stack-only instances.

`WordVec` stores the length and capacity of a container on the heap.
Thus, the heap pointer is always aligned to 2 bytes on most targets,
i.e. the least significant bit is always zero.
`WordVec` exploits this knowledge to represent small (stack-only) vecs
by storing the length as `1 | (length << 1)` in the first byte (for little-endian targets),
using the least significant bit to distinguish whether it is a heap pointer or a stack length.

## Supported platforms

Targets not meeting the following platform requirements will lead to compile error:

- Little-endian only
- `align_of::<usize>()` must be at least 2 bytes.
