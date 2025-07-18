//! `VecSet` is a vector-based set implementation which retains the order of inserted elements.

mod entry;
mod impls;
mod iter;
#[cfg(feature = "serde")]
mod serde;

use super::KeyedVecSet;
use alloc::vec::{self, Vec};
use core::borrow::Borrow;
use core::ops::RangeBounds;
use core::slice;

pub use self::entry::{Entry, OccupiedEntry, VacantEntry};
pub use self::iter::*;

/// A vector-based set implementation which retains the order of inserted elements.
///
/// Internally it is represented as a `Vec<T>` to support keys that are neither `Hash` nor `Ord`.
#[derive(Clone, Debug)]
pub struct VecSet<T> {
    base: KeyedVecSet<T, T>,
}

impl<T> VecSet<T> {
    /// Create a new set. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set: VecSet<&str> = VecSet::new();
    /// ```
    pub const fn new() -> Self {
        VecSet {
            base: KeyedVecSet::new(),
        }
    }

    /// Create a new set with capacity for `capacity` key-value pairs. (Does not allocate if
    /// `capacity` is zero.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set: VecSet<&str> = VecSet::with_capacity(10);
    /// assert_eq!(set.len(), 0);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        VecSet {
            base: KeyedVecSet::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the set can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set: VecSet<&str> = VecSet::with_capacity(10);
    /// assert_eq!(set.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Returns the number of elements in the set, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut a = VecSet::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1);
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut a = VecSet::new();
    /// assert!(a.is_empty());
    /// a.insert(1);
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Clears the set, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut a = VecSet::new();
    /// a.insert(1);
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.base.clear();
    }

    /// Shortens the set, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the set's current length, this has no effect.
    ///
    /// # Examples
    ///
    /// Truncating a four element set to two elements:
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c", "d"]);
    /// set.truncate(2);
    /// assert_eq!(set, VecSet::from(["a", "b"]));
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the set's current length:
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c", "d"]);
    /// set.truncate(8);
    /// assert_eq!(set, VecSet::from(["a", "b", "c", "d"]));
    /// ```
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `VecSet<T>`. The collection may reserve more space to speculatively avoid frequent
    /// reallocations. After calling `reserve`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a"]);
    /// set.reserve(10);
    /// assert!(set.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements to be inserted in
    /// the given `VecSet<T>`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore,
    /// capacity can not be relied upon to be precisely minimal. Prefer [`Self::reserve`] if future
    /// insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a"]);
    /// set.reserve_exact(10);
    /// assert!(set.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set: VecSet<i32> = VecSet::from([0, 1, 2, 3, 4, 5, 6, 7]);
    /// set.retain(|&e| e % 2 == 0);
    /// assert_eq!(set.len(), 4);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.base.retain(|k| f(k));
    }

    /// Shrinks the capacity of the set as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set: VecSet<i32> = VecSet::with_capacity(100);
    /// set.insert(1);
    /// set.insert(2);
    /// assert!(set.capacity() >= 100);
    /// set.shrink_to_fit();
    /// assert!(set.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.base.shrink_to_fit();
    }

    /// Shrinks the capacity of the set with a lower limit. It will drop down no lower than the
    /// supplied limit while maintaining the internal rules and possibly leaving some space in
    /// accordance with the resize policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set: VecSet<i32> = VecSet::with_capacity(100);
    /// set.insert(1);
    /// set.insert(2);
    /// assert!(set.capacity() >= 100);
    /// set.shrink_to(10);
    /// assert!(set.capacity() >= 10);
    /// set.shrink_to(0);
    /// assert!(set.capacity() >= 2);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.base.shrink_to(min_capacity);
    }

    /// Splits the set into two at the given index.
    ///
    /// Returns a newly allocated set containing the elements in the range `[at, len)`. After the
    /// call, the original set will be left containing the elements `[0, at)` with its previous
    /// capacity unchanged.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c"]);
    /// let set2 = set.split_off(1);
    /// assert_eq!(set, VecSet::from(["a"]));
    /// assert_eq!(set2, VecSet::from(["b", "c"]));
    /// ```
    pub fn split_off(&mut self, at: usize) -> VecSet<T> {
        VecSet {
            base: self.base.split_off(at),
        }
    }

    /// Removes the specified range from the vector in bulk, returning all removed elements as an
    /// iterator. If the iterator is dropped before being fully consumed, it drops the remaining
    /// removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the vector to optimize its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end point is greater
    /// than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut v = VecSet::from([1, 2, 3]);
    /// let u: VecSet<_> = v.drain(1..).collect();
    /// assert_eq!(v, VecSet::from([1]));
    /// assert_eq!(u, VecSet::from([2, 3]));
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, VecSet::new());
    /// ```
    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, T>
    where
        R: RangeBounds<usize>,
    {
        self.base.drain(range)
    }

    /// An iterator visiting all elements in insertion order. The iterator element type is
    /// `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let set = VecSet::from(["a", "b", "c"]);
    ///
    /// for elem in set.iter() {
    ///     println!("elem: {elem}");
    /// }
    /// ```
    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.base.iter()
    }

    /// Extracts a slice containing the set elements.
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let set = VecSet::from(["b", "a", "c"]);
    /// let slice = set.as_slice();
    /// assert_eq!(slice, ["a", "b", "c"]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        self.base.as_slice()
    }

    /// Copies the set elements into a new `Vec<T>`.
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let set = VecSet::from(["b", "a", "c"]);
    /// let vec = set.to_vec();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// // Here, `set` and `vec` can be modified independently.
    /// ```
    pub fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.iter().cloned().collect()
    }

    /// Takes ownership of the set and returns its elements as a `Vec<T>`.
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let set = VecSet::from(["b", "a", "c"]);
    /// let vec = set.into_vec();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.base.into_vec()
    }

    /// Takes ownership of provided vector and converts it into `VecSet`.
    ///
    /// # Safety
    ///
    /// The vector must be sorted and have no duplicate elements. One way to guarantee it is to sort the vector
    /// (e.g. by using [`[T]::sort`][slice-sort]) and then drop duplicate elements (e.g. by using
    /// [`Vec::dedup`]).
    ///
    /// # Example
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut vec = vec!["b", "a", "c", "b"];
    /// vec.sort();
    /// vec.dedup();
    /// // SAFETY: We've just deduplicated the vector.
    /// let set = unsafe { VecSet::from_sorted_vec(vec) };
    ///
    /// assert_eq!(set, VecSet::from(["b", "a", "c"]));
    /// ```
    ///
    /// [slice-sort]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort
    pub unsafe fn from_sorted_vec(vec: Vec<T>) -> Self {
        let base = unsafe { KeyedVecSet::from_sorted_vec(vec) };
        VecSet { base }
    }

    /// Returns based `KeyedVecSet`.
    ///
    /// Because `VecSet` itself never expose `&mut T`,
    /// this is useful when you need to edit keys, which are basically unsafe operations.
    pub fn as_mut_keyed_set(&mut self) -> &mut KeyedVecSet<T, T> {
        &mut self.base
    }
}

// Lookup operations.
impl<T> VecSet<T> {
    /// Return `true` if an equivalent to `key` exists in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert(1);
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&2), false);
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.contains_key(value)
    }

    /// Get the first element.
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a", "b"]);
    /// assert_eq!(set.first(), Some(&"a"));
    /// ```
    pub fn first(&self) -> Option<&T> {
        self.base.first()
    }

    /// Get the last element.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a", "b"]);
    /// assert_eq!(set.last(), Some(&"b"));
    /// set.pop();
    /// set.pop();
    /// assert_eq!(set.last(), None);
    /// ```
    pub fn last(&self) -> Option<&T> {
        self.base.last()
    }
}

// Lookup operations.
impl<T> VecSet<T> {
    /// Returns a reference to the value in the set, if any, that is equal to the given value.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Ord`] on the borrowed form
    /// *must* match those for the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.get(&2), Some(&2));
    /// assert_eq!(set.get(&4), None);
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q> + Ord,
        Q: ?Sized + Ord,
    {
        self.base.get(value)
    }

    /// Return references to the element stored at `index`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert(1);
    /// assert_eq!(set.get_index(0), Some(&1));
    /// assert_eq!(set.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<&T> {
        self.base.get_index(index)
    }

    /// Returns a reference to an element or subslice, without doing bounds
    /// checking.
    ///
    /// For a safe alternative see [`get_index`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [`get_index`]: VecSet::get_index
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        unsafe { self.base.get_unchecked(index) }
    }

    /// Returns the index and a reference to the value in the set, if any, that is equal to the
    /// given value.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Ord`] on the borrowed form
    /// *must* match those for the value type.
    ///
    /// # Errors
    ///
    /// Returns `Err(index)` if the value is not found, where `index` is the position where the value would be inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.get_full(&2), Ok((1, &2)));
    /// assert_eq!(set.get_full(&4), Err(3));
    /// ```
    pub fn get_full<Q>(&self, value: &Q) -> Result<(usize, &T), usize>
    where
        T: Borrow<Q> + Ord,
        Q: ?Sized + Ord,
    {
        self.base.get_full(value)
    }

    /// Return item index, if it exists in the set.
    ///
    /// # Errors
    ///
    /// Returns `Err(index)` if the value is not found, where `index` is the position where the value would be inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert("a");
    /// set.insert("b");
    /// assert_eq!(set.binary_search("a"), Ok(0));
    /// assert_eq!(set.binary_search("b"), Ok(1));
    /// assert_eq!(set.binary_search("c"), Err(2));
    /// ```
    pub fn binary_search<Q>(&self, value: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.binary_search(value)
    }

    /// Return the index of the value in the set, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.get_index_of(&2), Some(1));
    /// assert_eq!(set.get_index_of(&4), None);
    /// ```
    pub fn get_index_of<Q>(&self, value: &Q) -> Option<usize>
    where
        T: Borrow<Q> + Ord,
        Q: ?Sized + Ord,
    {
        self.binary_search(value).ok()
    }
}

// Removal operations.
impl<T> VecSet<T> {
    /// Removes the last element from the set and returns it, or [`None`] if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a", "b"]);
    /// assert_eq!(set.pop(), Some("b"));
    /// assert_eq!(set.pop(), Some("a"));
    /// assert!(set.is_empty());
    /// assert_eq!(set.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.base.pop()
    }

    /// Remove the element equivalent to `value`.
    ///
    /// Like `Vec::remove`, the element is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// Returns `true` if `value` was found in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from_iter([1, 2, 3, 4]);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// assert_eq!(set, VecSet::from_iter([1, 3, 4]));
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.remove(value).is_some()
    }

    /// Removes and returns the element at position `index` within the set, shifting all elements
    /// after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut v = VecSet::from(["a", "b", "c"]);
    /// assert_eq!(v.remove_index(1), "b");
    /// assert_eq!(v, VecSet::from(["a", "c"]));
    /// ```
    pub fn remove_index(&mut self, index: usize) -> T {
        self.base.remove_index(index)
    }

    /// Removes and returns the value in the set, if any, that is equal to the given one.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Ord`] on the borrowed form
    /// *must* match those for the value type.
    ///
    /// Like `Vec::remove`, the element is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.take(&2), Some(2));
    /// assert_eq!(set.take(&2), None);
    /// ```
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q> + Ord,
        Q: ?Sized + Ord,
    {
        self.base.remove(value)
    }
}

// Insertion operations.
impl<T> VecSet<T>
where
    T: Ord,
{
    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    ///
    /// - If the set did not previously contain this value, `true` is returned.
    /// - If the set already contained this value, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.base.insert(value).is_none()
    }

    /// Adds a value to the set, and returns the index where the value was inserted.
    ///
    /// Returns `(index, did_insert)`:
    /// - `index` is the position where the value is located
    /// - `did_insert` is `true` if the value was newly inserted, `false` if it already existed
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// assert_eq!(set.insert_full(2), (0, true));
    /// assert_eq!(set.insert_full(2), (0, false));
    /// assert_eq!(set.insert_full(1), (0, true));
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn insert_full(&mut self, value: T) -> (usize, bool) {
        let (index, old_value) = self.base.insert_full(value);
        (index, old_value.is_none())
    }

    /// Insert a value at the given index without any checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    /// - The index is within bounds (0 <= index <= len)
    /// - The value at the given index maintains the sorted order
    /// - The value does not already exist in the set
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// unsafe {
    ///     set.insert_index_unchecked(0, 1);
    ///     set.insert_index_unchecked(1, 3);
    ///     set.insert_index_unchecked(1, 2); // insert between 1 and 3
    /// }
    /// assert_eq!(set.as_slice(), &[1, 2, 3]);
    /// ```
    pub unsafe fn insert_index_unchecked(&mut self, index: usize, value: T) {
        unsafe { self.base.insert_index_unchecked(index, value) };
    }

    /// Gets the given value's corresponding entry in the set for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// for &word in &["a", "b", "c", "d"] {
    ///     set.entry(word).or_insert();
    /// }
    ///
    /// assert_eq!(set.len(), 4);
    /// ```
    pub fn entry(&mut self, value: T) -> Entry<T> {
        let index = self.binary_search(&value);
        unsafe { self.entry_index_unchecked(index, value) }
    }

    /// Get the entry in the set for insertion and/or in-place
    /// manipulation by given index and value. The index must be a valid result of [`Self::binary_search`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is valid and maintains the sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// unsafe {
    ///     match set.entry_index_unchecked(Err(0), 'b') {
    ///         vecset::set::Entry::Vacant(e) => {
    ///             e.insert();
    ///         }
    ///         vecset::set::Entry::Occupied(_) => {
    ///             panic!("unreachable");
    ///         }
    ///     }
    /// }
    ///
    /// assert!(set.contains(&'b'));
    /// ```
    pub unsafe fn entry_index_unchecked(
        &mut self,
        index: Result<usize, usize>,
        value: T,
    ) -> Entry<T> {
        match index {
            Ok(index) => Entry::Occupied(OccupiedEntry::new(self, index)),
            Err(index) => Entry::Vacant(VacantEntry::new(self, value, index)),
        }
    }
}

// Set operations.
impl<T> VecSet<T>
where
    T: Ord,
{
    /// Visits the values representing the difference, i.e., the values that are in `self` but not
    /// in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Can be seen as `a - b`.
    /// for x in a.difference(&b) {
    ///     println!("{x}"); // Print 1
    /// }
    ///
    /// let diff: VecSet<_> = a.difference(&b).collect();
    /// assert_eq!(diff, [1].iter().collect());
    ///
    /// // Note that difference is not symmetric,
    /// // and `b - a` means something else:
    /// let diff: VecSet<_> = b.difference(&a).collect();
    /// assert_eq!(diff, [4].iter().collect());
    /// ```
    pub fn difference<'a>(&'a self, other: &'a VecSet<T>) -> Difference<'a, T> {
        Difference::new(self, other)
    }

    /// Visits the values representing the intersection, i.e., the values that are both in `self`
    /// and `other`.
    ///
    /// When an equal element is present in `self` and `other` then the resulting `Intersection`
    /// may yield references to one or the other. This can be relevant if `T` contains fields which
    /// are not compared by its `Ord` implementation, and may hold different value between the two
    /// equal copies of `T` in the two sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Print 2, 3 in arbitrary order.
    /// for x in a.intersection(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let intersection: VecSet<_> = a.intersection(&b).collect();
    /// assert_eq!(intersection, [2, 3].iter().collect());
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a VecSet<T>) -> Intersection<'a, T> {
        if self.len() <= other.len() {
            Intersection::new(self, other)
        } else {
            Intersection::new(other, self)
        }
    }

    /// Visits the values representing the symmetric difference, i.e., the values that are in
    /// `self` or in `other` but not in both.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Print 1, 4 in arbitrary order.
    /// for x in a.symmetric_difference(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let diff1: VecSet<_> = a.symmetric_difference(&b).collect();
    /// let diff2: VecSet<_> = b.symmetric_difference(&a).collect();
    ///
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, [1, 4].iter().collect());
    /// ```
    pub fn symmetric_difference<'a>(&'a self, other: &'a VecSet<T>) -> SymmetricDifference<'a, T> {
        SymmetricDifference::new(self, other)
    }

    /// Visits the values representing the union, i.e., all the values in `self` or `other`,
    /// without duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order.
    /// for x in a.union(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let union: VecSet<_> = a.union(&b).collect();
    /// assert_eq!(union, [1, 2, 3, 4].iter().collect());
    /// ```
    pub fn union<'a>(&'a self, other: &'a VecSet<T>) -> Union<'a, T> {
        if self.len() >= other.len() {
            Union::new(self, other)
        } else {
            Union::new(other, self)
        }
    }

    /// Returns `true` if `self` has no elements in common with `other`. This is equivalent to
    /// checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let a = VecSet::from([1, 2, 3]);
    /// let mut b = VecSet::new();
    ///
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(4);
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(1);
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    pub fn is_disjoint(&self, other: &VecSet<T>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(v))
        } else {
            other.iter().all(|v| !self.contains(v))
        }
    }

    /// Returns `true` if the set is a subset of another, i.e., `other` contains at least all the
    /// values in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let sup = VecSet::from([1, 2, 3]);
    /// let mut set = VecSet::new();
    ///
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(2);
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(4);
    /// assert_eq!(set.is_subset(&sup), false);
    /// ```
    pub fn is_subset(&self, other: &VecSet<T>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(v))
        } else {
            false
        }
    }

    /// Returns `true` if the set is a superset of another, i.e., `self` contains at least all the
    /// values in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let sub = VecSet::from([1, 2]);
    /// let mut set = VecSet::new();
    ///
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(0);
    /// set.insert(1);
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(2);
    /// assert_eq!(set.is_superset(&sub), true);
    /// ```
    pub fn is_superset(&self, other: &VecSet<T>) -> bool {
        other.is_subset(self)
    }
}
