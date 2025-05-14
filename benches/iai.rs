mod impls;

pub struct IaiBlackBox;

impl impls::BlackBox for IaiBlackBox {
    fn black_box<T>(t: T) { iai::black_box(t); }
}

macro_rules! run_bench {
    (
        $module:ident;
        $bench_name:ident, $variant_name:ident;
        $($input_name:expr,)*;
        $($input_value:expr,)*;
        $($arg:expr,)*;
    ) => {
        paste::paste! {
            fn [<bench_ $module _ $bench_name _ $variant_name>]() {
                if <impls::$module::Benches as impls::Benches<IaiBlackBox>>::[<has_ $bench_name>]() {
                    $(let $input_name = $input_value;)*

                    let b = impls::$module::Benches;
                    impls::Benches::<IaiBlackBox>::$bench_name(&b, $($arg),*)
                }
            }
        }
    }
}

macro_rules! run_benches {
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
            $(
                $(
                    run_bench! {
                        std_vec;
                        $bench_name, $variant_name;
                        $($input_name,)*;
                        $($input_value,)*;
                        $($arg,)*;
                    }

                    run_bench! {
                        smallvec;
                        $bench_name, $variant_name;
                        $($input_name,)*;
                        $($input_value,)*;
                        $($arg,)*;
                    }

                    run_bench! {
                        wordvec;
                        $bench_name, $variant_name;
                        $($input_name,)*;
                        $($input_value,)*;
                        $($arg,)*;
                    }

                    run_bench! {
                        thinvec;
                        $bench_name, $variant_name;
                        $($input_name,)*;
                        $($input_value,)*;
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

impls::list_benches!(run_benches);
