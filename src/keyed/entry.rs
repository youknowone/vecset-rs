use super::{Keyed, KeyedVecSet};
use core::mem;
use core::ops::Deref;

/// `&mut V` wrapper to defer unsafe operations.
///
/// Accessing `&mut V` in `KeyedVecSet` is unsafe because changing key may cause the map to be unsorted or have duplicate keys.
/// Since most of operations in `Entry` returns `&mut V`, they must be regarded as unsafe in principle.
///
/// On the other hand, those entry operations are actually safe unless mutably accessing the returned value.
/// `Mut` helps to regard entry operations itself as safe, but accessing the returned value as unsafe.
pub struct Mut<'a, V>(&'a mut V);

impl<V> Mut<'_, V> {
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys. Those states will make `KeyedVecSet` working unspecified way. Those states will make `KeyedVecSet` working unspecified way.
    pub unsafe fn as_mut(&mut self) -> &mut V {
        self.0
    }
}

impl<V> Deref for Mut<'_, V> {
    type Target = V;

    fn deref(&self) -> &V {
        self.0
    }
}

/// Entry for an existing key-value pair or a vacant location to insert one.
#[derive(Debug)]
pub enum Entry<'a, K, V> {
    /// Existing slot with equivalent key.
    Occupied(OccupiedEntry<'a, K, V>),
    /// Vacant slot (no equivalent key in the map).
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Ord,
    V: Keyed<K>,
{
    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable
    /// reference to the value in the entry.
    ///
    /// # Panics
    ///
    /// Panics if the key of the provided value doesn't match the entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    ///
    /// map.entry("poneyland").or_insert(("poneyland", 3));
    /// assert_eq!(map["poneyland"].1, 3);
    ///
    /// unsafe { map.entry("poneyland").or_insert(("poneyland", 10)).as_mut().1 *= 2 };
    /// assert_eq!(map["poneyland"].1, 6);
    /// ```
    pub fn or_insert(self, default: V) -> Mut<'a, V> {
        assert!(self.key() == default.key());
        match self {
            Entry::Occupied(entry) => Mut(unsafe { entry.into_mut() }),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Panics
    ///
    /// Panics if the key of the value returned by the function doesn't match the entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::{Keyed, KeyedVecSet};
    ///
    /// let mut map: KeyedVecSet<&str, (&str, String)> = KeyedVecSet::new();
    /// let s = "hoho".to_string();
    ///
    /// map.entry("poneyland").or_insert_with(|| ("poneyland", s));
    ///
    /// assert_eq!(map["poneyland"].1, "hoho".to_string());
    /// ```
    pub fn or_insert_with<F>(self, call: F) -> Mut<'a, V>
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => Mut(unsafe { entry.into_mut() }),
            Entry::Vacant(entry) => {
                let value = call();
                assert!(&entry.key == value.key());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows for generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Panics
    ///
    /// Panics if the key of the value returned by the function doesn't match the entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, usize)> = KeyedVecSet::new();
    ///
    /// map.entry("poneyland").or_insert_with_key(|key| (key, key.chars().count()));
    ///
    /// assert_eq!(map["poneyland"].1, 9);
    /// ```
    pub fn or_insert_with_key<F>(self, default: F) -> Mut<'a, V>
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Entry::Occupied(entry) => Mut(unsafe { entry.into_mut() }),
            Entry::Vacant(entry) => {
                let value = default(&entry.key);
                assert!(&entry.key == value.key());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting if it was vacant, and returns
    /// the index of the entry and whether it was inserted.
    ///
    /// # Panics
    ///
    /// Panics if the key of the provided value doesn't match the entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::new();
    /// let (index, inserted) = map.entry("a").or_insert_full(("a", 1));
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, true);
    ///
    /// let (index, inserted) = map.entry("a").or_insert_full(("a", 2));
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, false);
    /// ```
    pub fn or_insert_full(self, value: V) -> (usize, bool) {
        assert!(self.key() == value.key());
        match self {
            Entry::Occupied(e) => (e.index, false),
            Entry::Vacant(e) => {
                let index = e.index;
                e.map.base.insert(index, value);
                (index, true)
            }
        }
    }

    /// Ensures a value is in the entry by inserting if it was vacant, and returns
    /// the index of the entry and whether it was inserted.
    ///
    /// This version doesn't check if the key matches.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the key of the provided value matches the entry's key.
    /// Failing to do so may result in a map with unsorted keys or duplicate keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::new();
    /// let (index, inserted) = unsafe { map.entry("a").or_insert_full_unchecked(("a", 1)) };
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, true);
    ///
    /// let (index, inserted) = unsafe { map.entry("a").or_insert_full_unchecked(("a", 2)) };
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, false);
    /// ```
    pub unsafe fn or_insert_full_unchecked(self, value: V) -> (usize, bool) {
        match self {
            Entry::Occupied(e) => (e.index, false),
            Entry::Vacant(e) => {
                let index = e.index;
                e.map.base.insert(index, value);
                (index, true)
            }
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns the index of the entry and whether it was inserted.
    ///
    /// # Panics
    ///
    /// Panics if the key of the value returned by the function doesn't match the entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::new();
    /// let (index, inserted) = map.entry("a").or_insert_with_full(|| ("a", 1));
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, true);
    ///
    /// let (index, inserted) = map.entry("a").or_insert_with_full(|| ("a", 2));
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, false);
    /// ```
    pub fn or_insert_with_full<F>(self, call: F) -> (usize, bool)
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(e) => (e.index, false),
            Entry::Vacant(e) => {
                let index = e.index;
                let value = call();
                assert!(&e.key == value.key());
                e.map.base.insert(index, value);
                (index, true)
            }
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns the index of the entry and whether it was inserted.
    ///
    /// This version doesn't check if the key matches.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the key of the value returned by the function matches the entry's key.
    /// Failing to do so may result in a map with unsorted keys or duplicate keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::new();
    /// let (index, inserted) = unsafe { map.entry("a").or_insert_with_full_unchecked(|| ("a", 1)) };
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, true);
    ///
    /// let (index, inserted) = unsafe { map.entry("a").or_insert_with_full_unchecked(|| ("a", 2)) };
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, false);
    /// ```
    pub unsafe fn or_insert_with_full_unchecked<F>(self, call: F) -> (usize, bool)
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(e) => (e.index, false),
            Entry::Vacant(e) => {
                let index = e.index;
                let value = call();
                e.map.base.insert(index, value);
                (index, true)
            }
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, &str> = KeyedVecSet::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Returns the index where the key-value pair exists or will be inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, &str> = KeyedVecSet::new();
    /// assert_eq!(map.entry("poneyland").index(), 0);
    /// ```
    pub fn index(&self) -> usize {
        match self {
            Entry::Occupied(entry) => entry.index(),
            Entry::Vacant(entry) => entry.index(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the
    /// map.
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys. Those states will make `KeyedVecSet` working unspecified way. Those states will make `KeyedVecSet` working unspecified way.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    ///
    /// unsafe {
    ///    map.entry("poneyland")
    ///        .and_modify(|e| { e.1 += 1 })
    /// }.or_insert(("poneyland", 42));
    /// assert_eq!(map["poneyland"].1, 42);
    ///
    /// unsafe {
    ///     map.entry("poneyland")
    ///        .and_modify(|e| { e.1 += 1 })
    /// }.or_insert(("poneyland", 42));
    /// assert_eq!(map["poneyland"].1, 43);
    /// ```
    pub unsafe fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut o) => {
                unsafe { f(o.get_mut()) };
                Entry::Occupied(o)
            }
            x => x,
        }
    }
}

/// A view into an occupied entry in a `KeyedVecSet`. It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, K, V> {
    map: &'a mut KeyedVecSet<K, V>,
    key: K,
    index: usize,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub(super) fn new(
        map: &'a mut KeyedVecSet<K, V>,
        key: K,
        index: usize,
    ) -> OccupiedEntry<'a, K, V> {
        OccupiedEntry { map, key, index }
    }

    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Gets the index of the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    /// assert_eq!(map.entry("poneyland").index(), 0);
    /// ```
    pub fn index(&self) -> usize {
        self.index
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, &str> = KeyedVecSet::new();
    /// map.insert("foo");
    ///
    /// if let Entry::Occupied(v) = map.entry("foo") {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.key
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get().1, 12);
    /// }
    /// ```
    pub fn get(&self) -> &V {
        &self.map[self.index]
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: Self::into_mut
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys. Those states will make `KeyedVecSet` working unspecified way.
    ///
    /// # Panics
    ///
    /// Panics if the key doesn't exist (which should not happen for an `OccupiedEntry`).
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    ///
    /// assert_eq!(map["poneyland"].1, 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     unsafe { o.get_mut().1 += 10 };
    ///     assert_eq!(o.get().1, 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     unsafe { o.get_mut().1 += 2 };
    /// }
    ///
    /// assert_eq!(map["poneyland"].1, 24);
    /// ```
    pub unsafe fn get_mut(&mut self) -> &mut V {
        unsafe { self.map.get_index_mut(self.index).expect("unexisting key") }
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: Self::get_mut
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys. Those states will make `KeyedVecSet` working unspecified way.
    ///
    /// # Panics
    ///
    /// Panics if the key doesn't exist (which should not happen for an `OccupiedEntry`).
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    ///
    /// assert_eq!(map["poneyland"].1, 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     unsafe { o.into_mut().1 += 10 };
    /// }
    ///
    /// assert_eq!(map["poneyland"].1, 22);
    /// ```
    pub unsafe fn into_mut(self) -> &'a mut V {
        unsafe { self.map.get_index_mut(self.index).expect("unexisting key") }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(("poneyland", 15)), ("poneyland", 12));
    /// }
    ///
    /// assert_eq!(map["poneyland"].1, 15);
    /// ```
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(unsafe { self.get_mut() }, value)
    }

    /// Removes and return the key-value pair stored in the map for this entry.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    /// map.entry("foo").or_insert(("foo", 13));
    /// map.entry("bar").or_insert(("bar", 14));
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// assert_eq!(map.binary_search("bar"), Ok(0));
    /// assert_eq!(map.binary_search("foo"), Ok(1));
    /// ```
    pub fn remove_entry(self) -> V {
        self.map.remove_index(self.index)
    }

    /// Removes the key-value pair stored in the map for this entry, and return the value.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    /// map.entry("poneyland").or_insert(("poneyland", 12));
    /// map.entry("foo").or_insert(("foo", 13));
    /// map.entry("bar").or_insert(("bar", 14));
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.remove().1, 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// assert_eq!(map.binary_search("bar"), Ok(0));
    /// assert_eq!(map.binary_search("foo"), Ok(1));
    /// ```
    pub fn remove(self) -> V {
        self.remove_entry()
    }
}

/// A view into a vacant entry in a `KeyedVecSet`. It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct VacantEntry<'a, K, V> {
    map: &'a mut KeyedVecSet<K, V>,
    key: K,
    index: usize,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub(super) fn new(
        map: &'a mut KeyedVecSet<K, V>,
        key: K,
        index: usize,
    ) -> VacantEntry<'a, K, V> {
        VacantEntry { map, key, index }
    }

    /// Gets a reference to the key that would be used when inserting a value through the
    /// `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, &str> = KeyedVecSet::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Return the index where the key-value pair will be inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<&str, &str> = KeyedVecSet::new();
    /// assert_eq!(map.entry("poneyland").index(), 0);
    /// ```
    pub fn index(&self) -> usize {
        self.index
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, &str> = KeyedVecSet::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns a mutable reference
    /// to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    /// use vecset::keyed::Entry;
    ///
    /// let mut map: KeyedVecSet<&str, (&str, u32)> = KeyedVecSet::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert(("poneyland", 37));
    /// }
    /// assert_eq!(map["poneyland"], ("poneyland", 37));
    /// ```
    pub fn insert(self, value: V) -> Mut<'a, V>
    where
        K: Ord,
        V: Keyed<K>,
    {
        self.map.base.insert(self.index, value);
        Mut(unsafe { self.map.base.get_unchecked_mut(self.index) })
    }
}
