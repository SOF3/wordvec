fn main() {
    println!("cargo::rustc-check-cfg=cfg(wordvec_bench_bench_partial)");
    println!("cargo::rustc-check-cfg=cfg(wordvec_bench_bench, values(any()))");
    println!("cargo::rustc-check-cfg=cfg(wordvec_bench_module_partial)");
    println!(
        r#"cargo::rustc-check-cfg=cfg(wordvec_bench_module, values("std_vec", "smallvec", "thinvec", "wordvec"))"#
    );
}
