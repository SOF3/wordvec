use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::{fmt, iter};

use serde::de::DeserializeSeed;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de};

use super::WordVec;

impl<T, const N: usize> Serialize for WordVec<T, N>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_slice().serialize(serializer)
    }
}

impl<'de, T, const N: usize> Deserialize<'de> for WordVec<T, N>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(DeVisitor(PhantomData))
    }

    fn deserialize_in_place<D>(deserializer: D, place: &mut Self) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(DeInPlaceVisitor(place))
    }
}

struct DeVisitor<T, const N: usize>(PhantomData<T>);

impl<'de, T, const N: usize> de::Visitor<'de> for DeVisitor<T, N>
where
    T: Deserialize<'de>,
{
    type Value = WordVec<T, N>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a sequence")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: de::SeqAccess<'de>,
    {
        let mut vec = WordVec::<T, N>::with_capacity(seq.size_hint().unwrap_or(N));
        let mut break_err = None;
        vec.extend(iter::from_fn(|| match seq.next_element() {
            Ok(Some(v)) => Some(v),
            Ok(None) => None,
            Err(err) => {
                break_err = Some(err);
                None
            }
        }));
        if let Some(err) = break_err {
            return Err(err);
        }
        Ok(vec)
    }
}

struct DeInPlaceVisitor<'place, T, const N: usize>(&'place mut WordVec<T, N>);

impl<'de, T, const N: usize> de::Visitor<'de> for DeInPlaceVisitor<'_, T, N>
where
    T: Deserialize<'de>,
{
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a sequence")
    }

    fn visit_seq<A>(self, seq: A) -> Result<Self::Value, A::Error>
    where
        A: de::SeqAccess<'de>,
    {
        let hint = seq.size_hint();
        let current_len = self.0.len();
        if let Some(hint) = hint
            && let Some(additional) = hint.checked_sub(current_len)
        {
            self.0.reserve(additional);
        }

        let (capacity_slice, current_len, mut set_len) =
            self.0.as_uninit_slice_with_length_setter();

        let (new_len, result) =
            try_visit_in_place_within_capacity(seq, capacity_slice, current_len);

        // SAFETY: try_visit_in_place must not return a length greater than
        // capacity_slice.len()
        unsafe { set_len.set_len(new_len) };

        if new_len < current_len {
            for place in &mut capacity_slice[new_len..current_len] {
                // SAFETY: these places were previously initialized,
                // but shall now be cleared.
                unsafe { place.assume_init_drop() };
            }
        }

        match result {
            TryVisitInPlaceResult::Fused => Ok(()),
            TryVisitInPlaceResult::HasMore(mut seq) => {
                // There may be more elements than the current reserved capacity.
                // This just means `seq.next_element()` has not returned a `None` yet;
                // it is possible that there are no additional items
                // because the reserved capacity is just enough.
                // In either case, we just use the slower `push` API
                // since we already tried our best to reserve the estimated capacity.
                while let Some(value) = seq.next_element()? {
                    self.0.push(value);
                }
                Ok(())
            }
            TryVisitInPlaceResult::Err(err) => Err(err),
        }
    }
}

fn try_visit_in_place_within_capacity<'de, A, T>(
    mut seq: A,
    capacity_slice: &mut [MaybeUninit<T>],
    current_len: usize,
) -> (usize, TryVisitInPlaceResult<'de, A>)
where
    A: de::SeqAccess<'de>,
    T: Deserialize<'de>,
{
    for (index, place) in capacity_slice[..current_len].iter_mut().enumerate() {
        // SAFETY: capacity_slice[..current_len] are all previously initialized.
        let place_ref = unsafe { place.assume_init_mut() };
        match seq.next_element_seed(InPlaceSeed(place_ref)) {
            Ok(Some(())) => {}
            Ok(None) => return (index, TryVisitInPlaceResult::Fused),
            Err(err) => return (index, TryVisitInPlaceResult::Err(err)),
        }
    }

    for (plus_index, place) in capacity_slice[current_len..].iter_mut().enumerate() {
        match seq.next_element() {
            Ok(Some(value)) => {
                place.write(value);
            }
            Ok(None) => return (current_len + plus_index, TryVisitInPlaceResult::Fused),
            Err(err) => return (current_len + plus_index, TryVisitInPlaceResult::Err(err)),
        }
    }

    (capacity_slice.len(), TryVisitInPlaceResult::HasMore(seq))
}

enum TryVisitInPlaceResult<'de, A: de::SeqAccess<'de>> {
    Fused,
    HasMore(A),
    Err(A::Error),
}

// Lifted from serde::core::private::seed
struct InPlaceSeed<'a, T: 'a>(&'a mut T);

impl<'de, T> DeserializeSeed<'de> for InPlaceSeed<'_, T>
where
    T: Deserialize<'de>,
{
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        T::deserialize_in_place(deserializer, self.0)
    }
}
