mod impls;

pub struct IaiBlackBox;

impl impls::BlackBox for IaiBlackBox {
    fn black_box<T>(t: T) { iai::black_box(t); }
}

macro_rules! run_bench {
    (
        $module:ident $module_strlit:literal;
        $bench_name:ident $bench_name_strlit:literal, $variant_name:ident;
        $($arg:expr,)*;
    ) => {
        paste::paste! {
            #[cfg(all(
                any(not(wordvec_bench_bench_partial), wordvec_bench_bench = $bench_name_strlit),
                any(not(wordvec_bench_module_partial), wordvec_bench_module = $module_strlit),
            ))]
            fn [<bench_ $module _ $bench_name _ $variant_name>]() {
                if <impls::$module::Benches as impls::Benches<IaiBlackBox>>::[<has_ $bench_name>]() {
                    impls::Benches::<IaiBlackBox>::$bench_name(impls::$module::Benches, $($arg),*)();
                }
            }

            #[cfg(not(all(
                any(not(wordvec_bench_bench_partial), wordvec_bench_bench = $bench_name_strlit),
                any(not(wordvec_bench_module_partial), wordvec_bench_module = $module_strlit),
            )))]
            fn [<bench_ $module _ $bench_name _ $variant_name>]() {}
        }
    }
}

macro_rules! run_benches {
    (
        $(
            $bench_name:ident $bench_name_strlit:literal
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
            $(
                $(
                    run_bench! {
                        std_vec "std_vec";
                        $bench_name $bench_name_strlit, $variant_name;
                        $($arg,)*;
                    }

                    run_bench! {
                        smallvec "smallvec";
                        $bench_name $bench_name_strlit, $variant_name;
                        $($arg,)*;
                    }

                    run_bench! {
                        wordvec "wordvec";
                        $bench_name $bench_name_strlit, $variant_name;
                        $($arg,)*;
                    }

                    run_bench! {
                        thinvec "thinvec";
                        $bench_name $bench_name_strlit, $variant_name;
                        $($arg,)*;
                    }
                )*
            )*

            iai::main!($($(
                [<bench_std_vec_ $bench_name _ $variant_name>],
                [<bench_smallvec_ $bench_name _ $variant_name>],
                [<bench_wordvec_ $bench_name _ $variant_name>],
                [<bench_thinvec_ $bench_name _ $variant_name>],
            )*)*);
        }
    }
}

impls::list_benches!(run_benches, IaiBlackbox);
