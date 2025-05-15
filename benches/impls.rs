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
    ($macro:ident) => {
        $macro! {
            from_exact_array_and_drop(
                array: [u16; 3],
            ) {
                exact: () => ([1, 2, 3]);
            }

            from_array_and_drop[const N: usize](
                array: [u16; N],
            ) {
                large: () => ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]);
                huge: (input = [3; 1027]) => (input);
            }

            from_iter_and_drop(
                input: impl Iterator<Item = u16>,
            ) {
                small: () => (1..4u16);
                large: () => (1..14u16);
                huge: () => (1..1028u16);
                huge_dyn: (iter = Box::new(1..1028u16) as Box<dyn Iterator<Item = u16>>) => (iter);
            }

            push_from_empty(
                input: impl Iterator<Item = u16>,
            ) {
                few: () => (Some(1u16).into_iter());
                small: () => (1..4u16);
                large: () => (1..14u16);
                huge: () => (1..1028u16);
                huge_dyn: (iter = Box::new(1..1028u16) as Box<dyn Iterator<Item = u16>>) => (iter);
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
            ) {
                $(
                    $variant_name:ident:
                    (
                        $(
                            $input_name:ident = $input_value:expr
                        ),* $(,)?
                    ) => (
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
                    fn $bench_name$(<$($generics)*>)?(&self, $($param_name: $param_ty),*);
                )*
            }
        }
    }
}

#[allow(unused_imports)]
pub(crate) use list_benches;

list_benches!(decl_benches);
