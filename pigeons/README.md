[![crates.io](https://img.shields.io/crates/v/pigeons?style=for-the-badge&logo=rust)](https://crates.io/crates/pigeons)
[![docs.rs](https://img.shields.io/docsrs/pigeons?style=for-the-badge&logo=docsdotrs)](https://docs.rs/pigeons)
[![License](https://img.shields.io/crates/l/pigeons?style=for-the-badge)](../LICENSE)

<!-- cargo-rdme start -->

# Pigeons

A proof logging library for [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB).

This library is a simple abstraction layer for writing proofs checkable with VeriPB.

## Features

- `short-keywords`: use short rule keywords, e.g., `p` instead of `pol`
- `serde`: add implementations for
  [`serde::Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html) and
  [`serde::Deserialize`](https://docs.rs/serde/latest/serde/trait.Deserialize.html) for library
  types
- `version2`: use VeriPB version 2 syntax instead of version 3

## Coverage of VeriPB Syntax

- [x] `f`: [`Proof::new`]
- [x] `pol`: [`Proof::operations`]
- [x] `rup`: [`Proof::reverse_unit_prop`]
- [x] `del`: [`Proof::delete_ids`], [`Proof::delete_id_range`], [`Proof::delete_constr`]
- [x] `delc`: [`Proof::delete_core_ids`]
- [x] `deld`: [`Proof::delete_derived_ids`]
- [x] `obju`: [`Proof::update_objective`]
- [x] `red`: [`Proof::redundant`]
- [x] `dom`: [`Proof::dominated`]
- [x] `core`: [`Proof::move_ids_to_core`], [`Proof::move_range_to_core`]
- [x] `sol`: [`Proof::solution`]
- [x] `solx`: [`Proof::exclude_solution`]
- [x] `soli`: [`Proof::improve_solution`]
- [x] `output`: [`Proof::output`], [`Proof::conclude`]
    - Guarantees:
        - [x] `NONE`
        - [x] `DERIVABLE`
        - [x] `EQUISATISFIABLE`
        - [x] `EQUIOPTIMAL`
        - [ ] `EQUIENUMERABLE` (documented but not yet implemented in VeriPB)
    - Types:
        - [x] none
        - [x] `FILE`
        - [x] `IMPLICIT`
        - [ ] `CONSTRAINTS` (documented but not yet implemented in VeriPB)
        - [ ] `PERMUTATION` (documented but not yet implemented in VeriPB)
- [x] `conclusion`: [`Proof::conclude`], [`Proof::new_with_conclusion`],
  [`Proof::update_default_conclusion`]
- [x] Sub-proofs
    - [ ] `scope leq` and `scope geq` in `red` and `dom` rules
- [x] `e`: [`Proof::equals`]
- [x] `ea`: [`Proof::equals_add`] (only with `version2` feature)
- [x] `eobj`: [`Proof::obj_equals`]
- [x] `i`: [`Proof::implied`]
- [x] `ia`: [`Proof::implied_add`]
- [x] `setlvl` (previously `#`): [`Proof::set_level`]
- [x] `wiplvl` (previously `w`): [`Proof::wipe_level`]
- [x] `strengthening_to_core`: [`Proof::strengthening_to_core`]
- [x] `def_order`
- [x] `load_order`
- [x] `pbc`
- [ ] `@` constraint labels

<!-- cargo-rdme end -->
