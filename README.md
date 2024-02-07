# vecset

[![Build Status](https://github.com/youknowone/vecset/workflows/ci/badge.svg)](https://github.com/youknowone/vecset/actions?query=workflow%3Aci)
[![crates.io](https://img.shields.io/crates/v/vecset)](https://crates.io/crates/vecset)
[![docs.rs](https://img.shields.io/docsrs/vecset)](https://docs.rs/vecset)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A vector-based sorted map and set implementation with zero dependencies and
support for `#![no_std]`.

The crate provides `VecMap`, `VecSet` and `KeyedVecSet` which are basically a map interface wrapper of sorted vectors. For all types, searching is O(n) using `Vec::binary_search`.

`VecMap<K, V>` is a map interface for a sorted vector `Vec<(K, V)>`. It is a wrapper of `KeyedVecSet` specialization `KeyedVecSet<K, (K, V)>`.

`VecSet<T>` is a set interface for a sorted vector `Vec<T>`. It is a wrapper of `KeyedVecSet` specialization `KeyedVecSet<T, T>`. This is also same as sorting-guaranteed `Vec<T>`.

`KeyedVecSet<K, V>` is a generalized interface of a sorted vector `Vec<V>` where `V: Keyed<K>`. It means `V` provides a key value using the key accessor `<V as Keyed<K>>::key() -> &K`. This is useful when value contains its own key. Accessing mutable reference of `KeyedVecSet` elements is unsafe because editing the key value may corrupt sorting of the container. The same functions will be safe for `VecMap` by hiding the key part from mutable reference.

Map keys are required to form a total order.

## Cargo features

The following features are available:

* `serde`: Provides [`Serialize`](https://docs.rs/serde/latest/serde/ser/trait.Serialize.html)
  and [`Deserialize`](https://docs.rs/serde/latest/serde/de/trait.Deserialize.html)
  implementations for `VecMap` and `VecSet`. This feature is disabled by
  default. Enabling it will pull in `serde` as a dependency.

## License

The source code of vecset is licensed under either of [Apache License,
Version 2.0](LICENSE-APACHE.md) or [MIT license](LICENSE-MIT) at your option.

Thanks to [vecmap-rs](https://github.com/martinohmann/vecmap-rs), the first version of this project based on.
