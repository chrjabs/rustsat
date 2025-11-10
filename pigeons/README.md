[![crates.io](https://img.shields.io/crates/v/pigeons?style=for-the-badge&logo=rust)](https://crates.io/crates/pigeons)
[![docs.rs](https://img.shields.io/docsrs/pigeons?style=for-the-badge&logo=docsdotrs)](https://docs.rs/pigeons)
[![License](https://img.shields.io/crates/l/pigeons?style=for-the-badge)](../LICENSE)

<!-- cargo-rdme start -->

# Pigeons

A proof logging library for [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB).

This library is a simple abstraction layer for writing proofs checkable with VeriPB.

## Features

- `serde`: add implementations for
  [`serde::Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html) and
  [`serde::Deserialize`](https://docs.rs/serde/latest/serde/trait.Deserialize.html) for library
  types
- `version2`: use VeriPB version 2 syntax instead of version 3

## Coverage of VeriPB Syntax

- [x] `f`: [`Proof::new`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.new)
- [x] `pol`: [`Proof::operations`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.operations)
- [x] `rup`: [`Proof::reverse_unit_prop`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.reverse_unit_prop)
- [x] `del`: [`Proof::delete_ids`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.delete_ids), [`Proof::delete_id_range`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.delete_id_range), [`Proof::delete_constr`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.delete_constr)
- [x] `delc`: [`Proof::delete_core_ids`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.delete_core_ids)
- [x] `deld`: [`Proof::delete_derived_ids`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.delete_derived_ids)
- [x] `obju`: [`Proof::update_objective`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.update_objective)
- [x] `red`: [`Proof::redundant`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.redundant)
- [x] `dom`: [`Proof::dominated`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.dominated)
- [x] `core`: [`Proof::move_ids_to_core`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.move_ids_to_core), [`Proof::move_range_to_core`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.move_range_to_core)
- [x] `sol`: [`Proof::solution`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.solution)
- [x] `solx`: [`Proof::exclude_solution`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.exclude_solution)
- [x] `soli`: [`Proof::improve_solution`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.improve_solution)
- [x] `output`: [`Proof::output`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.output), [`Proof::conclude`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.conclude)
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
- [x] `conclusion`: [`Proof::conclude`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.conclude), [`Proof::new_with_conclusion`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.new_with_conclusion),
  [`Proof::update_default_conclusion`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.update_default_conclusion)
- [x] Sub-proofs
    - [ ] `scope leq` and `scope geq` in `red` and `dom` rules
- [x] `e`: [`Proof::equals`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.equals)
- [x] `ea`: [`Proof::equals_add`] (only with `version2` feature)
- [x] `eobj`: [`Proof::obj_equals`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.obj_equals)
- [x] `i`: [`Proof::implied`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.implied)
- [x] `ia`: [`Proof::implied_add`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.implied_add)
- [x] `setlvl` (previously `#`): [`Proof::set_level`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.set_level)
- [x] `wiplvl` (previously `w`): [`Proof::wipe_level`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.wipe_level)
- [x] `strengthening_to_core`: [`Proof::strengthening_to_core`](https://docs.rs/pigeons/latest/pigeons/struct.Proof.html#method.strengthening_to_core)
- [x] `def_order`
- [x] `load_order`
- [x] `pbc`
- [ ] `@` constraint labels

<!-- cargo-rdme end -->
