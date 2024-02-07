# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.2](https://github.com/youknowone/vecset-rs/compare/v0.0.1...v0.0.2) - 2024-02-07

### Added
- *(set)* add `VecSet::from_vec_unchecked` ([#27](https://github.com/youknowone/vecset-rs/pull/27))
- *(map)* avoid allocations in conversion from vector or slice ([#16](https://github.com/youknowone/vecset-rs/pull/16))
- *(map)* impl `ExactSizeIterator` and `Debug` for `Drain`
- *(map)* add `insert_at`
- add `truncate`
- add `swap_indices`
- *(map)* add `MutableKeys` trait ([#12](https://github.com/youknowone/vecset-rs/pull/12))
- *(set)* implement `Clone` for `IntoIter`
- add `as_slice`, `to_vec` and `into_vec` methods
- *(entry)* add `into_key` method to `OccupiedEntry`
- add sort methods
- implement `Clone` for all immutable iterators
- add `VecSet` ([#5](https://github.com/youknowone/vecset-rs/pull/5))
- add `split_off`
- add `remove_index`
- add `drain`
- add `shrink_to_fit` and `shrink_to`
- add `retain`
- add `vecmap!` macro
- add `insert_full`
- add `serde` feature
- add iterators
- add `Entry` API
- add `VecMap` and basic operations

### Fixed
- *(map)* [**breaking**] update API of VecMap::retain to be consistent with std ([#25](https://github.com/youknowone/vecset-rs/pull/25))
- *(map)* prevent segmentation fault in `VecMap::as_slice` ([#19](https://github.com/youknowone/vecset-rs/pull/19))
- *(set)* remove unnecessary trait bounds from `Drain`
- remove unnecessary usages of `mem::transmute`
- remove some needless borrows
- manually implement `PartialEq` and `Eq`

### Other
- keywords limit to 5
- Add get_unchecked
- Add {VecMap,VecSet}::as_mut_keyed_set
- Revise map based on KeyedVecSet
- Revise VecSet on KeyedVecSet
- First KeyedVecSet
- Prepare to start a new library: vecset
- release ([#28](https://github.com/youknowone/vecset-rs/pull/28))
- *(release)* switch to release-plz
- avoid unnecessary allocations in `Vec{Map,Set}::into_vec`
- *(main)* release 0.2.0 ([#26](https://github.com/youknowone/vecset-rs/pull/26))
- fix minor typos and formatting issues
- *(main)* release 0.1.15 ([#23](https://github.com/youknowone/vecset-rs/pull/23))
- inline `get_slot{,_mut}` at call sites
- improve internal `Slot<K, V>` API ([#22](https://github.com/youknowone/vecset-rs/pull/22))
- *(main)* release 0.1.14 ([#21](https://github.com/youknowone/vecset-rs/pull/21))
- apply new clippy lint suggestions
- run miri ([#20](https://github.com/youknowone/vecset-rs/pull/20))
- *(main)* release 0.1.13 ([#17](https://github.com/youknowone/vecset-rs/pull/17))
- *(main)* release 0.1.12 ([#15](https://github.com/youknowone/vecset-rs/pull/15))
- enable `doc_auto_cfg` feature for `docs.rs`
- *(macros)* align internal impls
- *(main)* release 0.1.11 ([#14](https://github.com/youknowone/vecset-rs/pull/14))
- *(main)* release 0.1.10 ([#13](https://github.com/youknowone/vecset-rs/pull/13))
- *(main)* release 0.1.9 ([#11](https://github.com/youknowone/vecset-rs/pull/11))
- *(main)* release 0.1.8 ([#10](https://github.com/youknowone/vecset-rs/pull/10))
- enable `clippy::pedantic` warnings
- *(map)* remove note about computation cost
- *(main)* release 0.1.7 ([#9](https://github.com/youknowone/vecset-rs/pull/9))
- *(test)* switch to `serde_test`
- add missing word in module docs
- *(main)* release 0.1.6 ([#8](https://github.com/youknowone/vecset-rs/pull/8))
- *(map)* rename `entries` to `base`
- *(main)* release 0.1.5 ([#7](https://github.com/youknowone/vecset-rs/pull/7))
- *(main)* release 0.1.4 ([#6](https://github.com/youknowone/vecset-rs/pull/6))
- add links to more type docs
- add links to more type docs
- fix broken link to `IndexSet` docs
- *(main)* release 0.1.3 ([#4](https://github.com/youknowone/vecset-rs/pull/4))
- don't access underlying vec directly in entry
- *(main)* release 0.1.2 ([#3](https://github.com/youknowone/vecset-rs/pull/3))
- add documentation link to `Cargo.toml`
- *(main)* release 0.1.1 ([#2](https://github.com/youknowone/vecset-rs/pull/2))
- fix crate categories
- fix license identifier
- *(main)* release 0.1.0 ([#1](https://github.com/youknowone/vecset-rs/pull/1))
- prepare release
- update README
- dual-license under MIT and Apache 2.0
- rearrange methods into impl blocks
- use `Slot` type for map entries
- initial commit
# Changelog

Forked [vecmap-rs](https://github.com/martinohmann/vecmap-rs) v0.2.1
