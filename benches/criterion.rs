use std::time::Duration;

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

mod impls;

pub struct CriterionBlackBox;

impl impls::BlackBox for CriterionBlackBox {
    fn black_box<T>(t: T) { criterion::black_box(t); }
}

macro_rules! run_bench {
    (
        $impl_name:literal, $module:ident, $group:ident;
        $bench_name:ident, $variant_name:ident, $vec:path;
        $($init_arg:expr,)*;
    ) => {
        if paste::paste!(<impls::$module::Benches as impls::Benches<CriterionBlackBox>>::[<has_ $bench_name>]()) {
            $group.measurement_time(Duration::from_secs(10));
            $group.bench_function(BenchmarkId::new(stringify!($variant_name), $impl_name), |b| {
                b.iter_batched(
                    || {
                        impls::Benches::<CriterionBlackBox>::$bench_name(impls::$module::Benches, $($init_arg),*)
                    },
                    |f| f(),
                    BatchSize::SmallInput,
                );
            });
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
                #[cfg(any(not(wordvec_bench_bench_partial), wordvec_bench_bench = $bench_name_strlit))]
                fn [<bench_ $bench_name>](c: &mut Criterion) {
                    let mut group = c.benchmark_group($bench_name_strlit);

                    $(
                        #[cfg(any(not(wordvec_bench_module_partial), wordvec_bench_module = "std_vec"))]
                        run_bench! {
                            "std::vec", std_vec, group;
                            $bench_name, $variant_name, ::std::vec::Vec<u16>;
                            $($arg,)*;
                        }

                        #[cfg(any(not(wordvec_bench_module_partial), wordvec_bench_module = "smallvec"))]
                        run_bench! {
                            "smallvec", smallvec, group;
                            $bench_name, $variant_name, ::smallvec::SmallVec<u16>;
                            $($arg,)*;
                        }

                        #[cfg(any(not(wordvec_bench_module_partial), wordvec_bench_module = "wordvec"))]
                        run_bench! {
                            "wordvec", wordvec, group;
                            $bench_name, $variant_name, ::wordvec::WordVec<u16>;
                            $($arg,)*;
                        }

                        #[cfg(any(not(wordvec_bench_module_partial), wordvec_bench_module = "thinvec"))]
                        run_bench! {
                            "thinvec", thinvec, group;
                            $bench_name, $variant_name, ::thin_vec::ThinVec<u16>;
                            $($arg,)*;
                        }
                    )*
                }

                #[cfg(not(any(not(wordvec_bench_bench_partial), wordvec_bench_bench = $bench_name_strlit)))]
                fn [<bench_ $bench_name>](_: &mut Criterion) {}
            )*

            criterion_group! {
                name = criterion_benches;
                config = Criterion::default();
                targets = $(
                    [<bench_ $bench_name>],
                )*
            }
        }
    }
}

impls::list_benches!(run_benches, CriterionBlackbox);

criterion_main!(criterion_benches);
