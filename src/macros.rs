/// Creates a [`WordVec`](super::WordVec) containing the elements.
///
/// Like the std `vec!` macro,
/// the `wordvec![x; n]` syntax always evaluates `x` once,
/// even if `n` is zero, then clones `x` for `n` times.
///
/// # Examples
/// ```
/// # use wordvec::{wordvec, WordVec};
///
/// fn assert_equal<const N: usize>(wv: WordVec<i32, N>, slice: &[i32]) {
///     assert_eq!(wv.as_slice(), slice);
/// }
///
/// assert_equal::<3>(wordvec![], &[]);
/// assert_equal::<3>(wordvec![1], &[1]);
/// assert_equal::<3>(wordvec![2, 3], &[2, 3]);
/// assert_equal::<1>(wordvec![2, 3], &[2, 3]);
/// assert_equal::<3>(wordvec![4; 5], &[4; 5]);
/// ```
#[macro_export]
macro_rules! wordvec {
    (@count $_:expr) => { 1usize };

    () => {
        $crate::WordVec::new()
    };

    ($elem:expr; $n:expr) => {{
        $crate::WordVec::from_elem($elem, $n)
    }};

    ($($x:expr),+ $(,)?) => {{
        let len = (0usize $(+ $crate::wordvec!(@count $x))*);
        let mut output = $crate::WordVec::new();
        if len <= output.capacity() {
            output = $crate::WordVec::from([$($x),*]);
        } else {
            output.reserve(len);
            $(output.push($x);)*
        }
        output
    }};
}
