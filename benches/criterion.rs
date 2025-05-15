use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

mod impls;

pub struct CriterionBlackBox;

impl impls::BlackBox for CriterionBlackBox {
    fn black_box<T>(t: T) { criterion::black_box(t); }
}

macro_rules! run_bench {
    (
        $impl_name:literal, $module:ident, $group:ident;
        $bench_name:ident, $variant_name:ident;
        $($input_key:ident,)*;
        $($input_value:expr,)*;
        $($init_arg:expr,)*;
    ) => {
        if paste::paste!(<impls::$module::Benches as impls::Benches<CriterionBlackBox>>::[<has_ $bench_name>]()) {
            $group.bench_function(BenchmarkId::new(stringify!($variant_name), $impl_name), |b| {
                b.iter_batched(
                    || criterion::black_box(($($input_value,)*)),
                    |($($input_key,)*)| {
                        let b = impls::$module::Benches;
                        impls::Benches::<CriterionBlackBox>::$bench_name(&b, $($init_arg),*)
                    },
                    BatchSize::SmallInput,
                );
            });
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
                fn [<bench_ $bench_name>](c: &mut Criterion) {
                    let mut group = c.benchmark_group(stringify!($bench_name));

                    $(
                        run_bench! {
                            "std::vec", std_vec, group;
                            $bench_name, $variant_name;
                            $($input_name,)*;
                            $($input_value,)*;
                            $($arg,)*;
                        }

                        run_bench! {
                            "smallvec", smallvec, group;
                            $bench_name, $variant_name;
                            $($input_name,)*;
                            $($input_value,)*;
                            $($arg,)*;
                        }

                        run_bench! {
                            "wordvec", wordvec, group;
                            $bench_name, $variant_name;
                            $($input_name,)*;
                            $($input_value,)*;
                            $($arg,)*;
                        }

                        run_bench! {
                            "thinvec", thinvec, group;
                            $bench_name, $variant_name;
                            $($input_name,)*;
                            $($input_value,)*;
                            $($arg,)*;
                        }
                    )*
                }
            )*

            criterion_group! {
                name = criterion_benches;
                config = Criterion::default();
                targets = $([<bench_ $bench_name>],)*
            }
        }
    }
}

impls::list_benches!(run_benches);

criterion_main!(criterion_benches);
