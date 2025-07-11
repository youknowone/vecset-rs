//! Entry API for `VecSet`

use super::VecSet;

/// A view into a single entry in a set, which may either be vacant or occupied.
///
/// This enum is constructed from the [`entry`] method on [`VecSet`].
///
/// [`entry`]: VecSet::entry
pub enum Entry<'a, T> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, T>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, T>),
}

impl<'a, T> Entry<'a, T>
where
    T: Ord,
{
    /// Ensures a value is in the entry by inserting if it was vacant, and returns
    /// a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// let value = set.entry("a").or_insert();
    /// assert_eq!(value, &"a");
    ///
    /// assert!(set.contains(&"a"));
    /// ```
    pub fn or_insert(self) -> &'a T {
        match self {
            Entry::Occupied(e) => &e.set.base.base[e.index],
            Entry::Vacant(e) => {
                let index = e.index;
                e.set.base.base.insert(index, e.value);
                &e.set.base.base[index]
            }
        }
    }

    /// Ensures a value is in the entry by inserting if it was vacant, and returns
    /// the index of the value and whether it was inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// let (index, inserted) = set.entry("a").or_insert_full();
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, true);
    ///
    /// let (index, inserted) = set.entry("a").or_insert_full();
    /// assert_eq!(index, 0);
    /// assert_eq!(inserted, false);
    /// ```
    pub fn or_insert_full(self) -> (usize, bool) {
        match self {
            Entry::Occupied(e) => (e.index, false),
            Entry::Vacant(e) => {
                let index = e.index;
                e.set.base.base.insert(index, e.value);
                (index, true)
            }
        }
    }

    /// Returns the entry's index within the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert("a");
    /// set.insert("b");
    /// assert_eq!(set.entry("a").index(), 0);
    /// assert_eq!(set.entry("b").index(), 1);
    /// assert_eq!(set.entry("c").index(), 2);
    /// ```
    pub fn index(&self) -> usize {
        match self {
            Entry::Occupied(e) => e.index(),
            Entry::Vacant(e) => e.index(),
        }
    }
}

/// A view into an occupied entry in a `VecSet`.
/// It is part of the [`Entry`] enum.
pub struct OccupiedEntry<'a, T> {
    set: &'a mut VecSet<T>,
    index: usize,
}

impl<'a, T> OccupiedEntry<'a, T> {
    pub(super) fn new(set: &'a mut VecSet<T>, index: usize) -> Self {
        OccupiedEntry { set, index }
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert("a");
    ///
    /// match set.entry("a") {
    ///     vecset::set::Entry::Occupied(e) => {
    ///         assert_eq!(e.get(), &"a");
    ///     }
    ///     vecset::set::Entry::Vacant(_) => unreachable!(),
    /// }
    /// ```
    pub fn get(&self) -> &T {
        &self.set.base.base[self.index]
    }

    /// Gets the index of the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert("a");
    /// set.insert("b");
    ///
    /// match set.entry("b") {
    ///     vecset::set::Entry::Occupied(e) => {
    ///         assert_eq!(e.index(), 1);
    ///     }
    ///     vecset::set::Entry::Vacant(_) => unreachable!(),
    /// }
    /// ```
    pub fn index(&self) -> usize {
        self.index
    }

    /// Take the ownership of the value from the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c"]);
    ///
    /// match set.entry("b") {
    ///     vecset::set::Entry::Occupied(e) => {
    ///         assert_eq!(e.remove(), "b");
    ///     }
    ///     vecset::set::Entry::Vacant(_) => unreachable!(),
    /// }
    ///
    /// assert_eq!(set, VecSet::from(["a", "c"]));
    /// ```
    pub fn remove(self) -> T {
        self.set.base.remove_index(self.index)
    }
}

/// A view into a vacant entry in a `VecSet`.
/// It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, T> {
    set: &'a mut VecSet<T>,
    value: T,
    index: usize,
}

impl<'a, T> VacantEntry<'a, T>
where
    T: Ord,
{
    pub(super) fn new(set: &'a mut VecSet<T>, value: T, index: usize) -> Self {
        VacantEntry { set, value, index }
    }

    /// Gets the index where the value would be inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert("a");
    /// set.insert("c");
    ///
    /// match set.entry("b") {
    ///     vecset::set::Entry::Vacant(e) => {
    ///         assert_eq!(e.index(), 1);
    ///     }
    ///     vecset::set::Entry::Occupied(_) => unreachable!(),
    /// }
    /// ```
    pub fn index(&self) -> usize {
        self.index
    }

    /// Take ownership of the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// match set.entry("a") {
    ///     vecset::set::Entry::Vacant(e) => {
    ///         assert_eq!(e.into_value(), "a");
    ///     }
    ///     vecset::set::Entry::Occupied(_) => unreachable!(),
    /// }
    /// ```
    pub fn into_value(self) -> T {
        self.value
    }

    /// Sets the value of the entry and returns a reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// match set.entry("a") {
    ///     vecset::set::Entry::Vacant(e) => {
    ///         e.insert();
    ///     }
    ///     vecset::set::Entry::Occupied(_) => unreachable!(),
    /// }
    ///
    /// assert!(set.contains(&"a"));
    /// ```
    pub fn insert(self) {
        self.set.base.base.insert(self.index, self.value);
    }

    /// Sets the value of the entry and returns an `OccupiedEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// match set.entry("a") {
    ///     vecset::set::Entry::Vacant(e) => {
    ///         let occupied = e.insert_entry();
    ///         assert_eq!(occupied.get(), &"a");
    ///     }
    ///     vecset::set::Entry::Occupied(_) => unreachable!(),
    /// }
    /// ```
    pub fn insert_entry(self) -> OccupiedEntry<'a, T> {
        let index = self.index;
        self.set.base.base.insert(index, self.value);
        OccupiedEntry::new(self.set, index)
    }
}
