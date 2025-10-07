#[path = "impls/smallvec.rs"]
pub mod smallvec;
#[path = "impls/std_vec.rs"]
pub mod std_vec;
#[path = "impls/thinvec.rs"]
pub mod thinvec;
#[path = "impls/wordvec.rs"]
pub mod wordvec;

pub trait BlackBox {
    fn black_box<T>(t: T);
}

#[allow(unused_macros)]
macro_rules! list_benches {
    ($macro:ident, $blackbox:ident) => {
        $macro! {
            from_exact_array_and_drop(
                array: [u16; 3],
            ) {
                exact: ([1, 2, 3]);
            }

            from_array_and_drop[const N: usize](
                array: [u16; N],
            ) {
                large: ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]);
                huge: ([3; 1027]);
            }

            from_iter_and_drop(
                input: impl Iterator<Item = u16>,
            ) {
                empty: (std::iter::empty());
                small: (1..4u16);
                large: (1..14u16);
                huge: (1..1028u16);
                huge_dyn: (Box::new(1..1028u16) as Box<dyn Iterator<Item = u16>>);
            }

            push_from_empty(
                input: impl Iterator<Item = u16>,
            ) {
                few: (Some(1u16).into_iter());
                small: (1..4u16);
                large: (1..14u16);
                huge: (1..1028u16);
                huge_dyn: (Box::new(1..1028u16) as Box<dyn Iterator<Item = u16>>);
            }

            remove_first(size: u16) {
                few: (1);
                small: (3);
                large: (14);
                huge: (1027);
            }

            remove_second(size: u16) {
                small: (3);
                large: (14);
                huge: (1027);
            }

            inc_many_flat(each_size: u16, vec_count: usize) {
                empty: (0, 1000);
                small: (3, 1000);
                large: (14, 1000);
                huge: (1027, 1000);
            }

            inc_many_flat_pattern(pattern: &[u16], vec_count: usize) {
                all_small: (&[0, 2, 3, 1], 1000);
                mixed: (&[0, 14, 3, 1027], 1000);
            }

            shrink_to(len: u16, initial_cap: usize, new_cap: usize) {
                small_to_small: (2, 2, 2);
                small_to_large_noop: (2, 2, 8);
                large_to_small: (2, 8, 2);
                large_to_large: (2, 8, 6);
                large_to_large_noop: (8, 8, 2);
            }

            shrink_to_fit(len: u16, initial_cap: usize) {
                small: (2, 2);
                large_to_small: (2, 8);
                large_to_large: (4, 8);
                large_to_large_noop: (8, 8);
            }
        }
    };
}

macro_rules! decl_benches {
    (
        $(
            $bench_name:ident
            $([$($generics:tt)*])?
            (
                $(
                    $param_name:ident: $param_ty:ty
                ),* $(,)?
            )
            {
                $(
                    $variant_name:ident:
                    (
                        $($arg:expr),* $(,)?
                    );
                )*
            }
        )*
    ) => {
        paste::paste! {
            pub trait Benches<B: BlackBox> {
                $(
                    fn [<has_ $bench_name>]() -> bool { true }

                    #[allow(clippy::wrong_self_convention)]
                    fn $bench_name$(<$($generics)*>)?(self, $($param_name: $param_ty),*) -> impl FnOnce();
                )*
            }
        }
    }
}

#[allow(unused_imports)]
pub(crate) use list_benches;

list_benches!(decl_benches, B);
