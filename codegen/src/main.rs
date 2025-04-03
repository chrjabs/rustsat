fn main() {
    // Check if current directory has a Cargo.toml with [workspace]
    let cargo_toml_path = std::env::current_dir().unwrap().join("Cargo.toml");
    let cargo_toml_content =
        std::fs::read_to_string(cargo_toml_path).expect("Failed to read Cargo.toml");
    if !cargo_toml_content.contains("[workspace]") {
        panic!(
            "Cargo.toml does not contain [workspace] (you must run codegen from the workspace root)"
        );
    }

    let path = "capi/src/encodings/totalizer.rs";
    capi_card_enc(&mut file(path), "Totalizer", "tot", true, true)
        .expect("failed to write card bindings");
    rustfmt(path);
}

fn file(path: &str) -> impl std::io::Write {
    std::io::BufWriter::new(std::fs::File::create(path).expect("could not open file"))
}

/// Runs `rustfmt` on a generated file
fn rustfmt(path: &str) {
    // Run rustfmt on the generated file
    let status = std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .expect("Failed to execute rustfmt");

    if !status.success() {
        eprintln!("rustfmt failed on file {path} with exit code: {status}");
    }
}

fn capi_card_enc<W: std::io::Write>(
    writer: &mut W,
    enc: &str,
    id: &str,
    ub: bool,
    lb: bool,
) -> std::io::Result<()> {
    writeln!(
        writer,
        r#"use std::ffi::{{c_int, c_void}};

        use rustsat::{{
            encodings::card::{{
                {} {} EncodeIncremental,
                {enc},
            }},
            types::Lit,
        }};

        use super::{{CClauseCollector, ClauseCollector, MaybeError, VarManager}};
        "#,
        if ub {
            "BoundUpper, BoundUpperIncremental,"
        } else {
            ""
        },
        if lb {
            "BoundLower, BoundLowerIncremental,"
        } else {
            ""
        },
    )?;
    writeln!(
        writer,
        r#"
        /// Creates a new [`{enc}`] cardinality encoding
        #[no_mangle]
        #[allow(clippy::missing_safety_doc)]
        pub unsafe extern "C" fn {id}_new() -> *mut {enc} {{
            Box::into_raw(Box::default())
        }}
        "#
    )?;
    writeln!(
        writer,
        r#"
        /// Frees the memory associated with a [`{enc}`]
        ///
        /// # Safety
        ///
        /// `{id}` must be a return value of [`{id}_new`] and cannot be used afterwards again.
        #[no_mangle]
        pub unsafe extern "C" fn {id}_drop({id}: *mut {enc}) {{
            drop(Box::from_raw({id}));
        }}
        "#
    )?;
    writeln!(
        writer,
        r#"
        /// Reserves all auxiliary variables that the encoding might need
        ///
        /// All calls to [`{id}_encode_ub`] following a call to this function are guaranteed to not increase
        /// the value of `n_vars_used`. This does _not_ hold if [`{id}_add`] is called in between
        ///
        /// # Safety
        ///
        /// `{id}` must be a return value of [`{id}_new`] that [`{id}_drop`] has not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn {id}_reserve({id}: *mut {enc}, n_vars_used: &mut u32) {{
            let mut var_manager = VarManager::new(n_vars_used);
            (*{id}).reserve(&mut var_manager);
        }}
        "#
    )?;
    writeln!(
        writer,
        r#"
        /// Adds a new input literal to a [`{enc}`]
        ///
        /// # Errors
        ///
        /// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
        ///     [`MaybeError::InvalidLiteral`] is returned
        ///
        /// # Safety
        ///
        /// `{id}` must be a return value of [`{id}_new`] that [`{id}_drop`] has not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn {id}_add({id}: *mut {enc}, lit: c_int) -> MaybeError {{
            let Ok(lit) = Lit::from_ipasir(lit) else {{
                return MaybeError::InvalidLiteral;
            }};
            (*{id}).extend([lit]);
            MaybeError::Ok
        }}
        "#
    )?;
    if ub {
        writeln!(
            writer,
            r#"
            /// Lazily builds the _change in_ cardinality encoding to enable upper bounds in a given range. A
            /// change might be added literals or changed bounds.
            ///
            /// The min and max bounds are inclusive. After a call to [`{id}_encode_ub`] with `min_bound=2` and
            /// `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
            ///
            /// Clauses are returned via the `collector`. The `collector` function should expect clauses to be
            /// passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
            /// passed as the first argument and the `collector_data` as a second.
            ///
            /// `n_vars_used` must be the number of variables already used and will be incremented by the
            /// number of variables used up in the encoding.
            ///
            /// # Safety
            ///
            /// `{id}` must be a return value of [`{id}_new`] that [`{id}_drop`] has not yet been called on.
            ///
            /// # Panics
            ///
            /// - If `min_bound > max_bound`.
            /// - If the encoding ran out of memory
            #[no_mangle]
            pub unsafe extern "C" fn {id}_encode_ub(
                {id}: *mut {enc},
                min_bound: usize,
                max_bound: usize,
                n_vars_used: &mut u32,
                collector: CClauseCollector,
                collector_data: *mut c_void,
            ) {{
                assert!(min_bound <= max_bound);
                let mut collector = ClauseCollector::new(collector, collector_data);
                let mut var_manager = VarManager::new(n_vars_used);
                (*{id})
                    .encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager)
                    .expect("clause collector ran out of memory");
            }}
            "#
        )?;
        writeln!(
            writer,
            r#"
            /// Returns an assumption/unit for enforcing an upper bound (`sum of lits <= ub`). Make sure that
            /// [`{id}_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
            /// [`MaybeError::NotEncoded`] will be returned.
            ///
            /// # Safety
            ///
            /// `{id}` must be a return value of [`{id}_new`] that [`{id}_drop`] has not yet been called on.
            #[no_mangle]
            pub unsafe extern "C" fn {id}_enforce_ub(
                {id}: *mut {enc},
                ub: usize,
                assump: &mut c_int,
            ) -> MaybeError {{
                match (*{id}).enforce_ub(ub) {{
                    Ok(assumps) => {{
                        debug_assert_eq!(assumps.len(), 1);
                        *assump = assumps[0].to_ipasir();
                        MaybeError::Ok
                    }}
                    Err(err) => err.into(),
                }}
            }}
            "#
        )?;
    }
    if lb {
        writeln!(
            writer,
            r#"
            /// Lazily builds the _change in_ cardinality encoding to enable lower bounds in a given range. A
            /// change might be added literals or changed bounds.
            ///
            /// The min and max bounds are inclusive. After a call to [`{id}_encode_lb`] with `min_bound=2` and
            /// `max_bound=4` bound including `>= 2` and `>= 4` can be enforced.
            ///
            /// Clauses are returned via the `collector`. The `collector` function should expect clauses to be
            /// passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
            /// passed as the first argument and the `collector_data` as a second.
            ///
            /// `n_vars_used` must be the number of variables already used and will be incremented by the
            /// number of variables used up in the encoding.
            ///
            /// # Safety
            ///
            /// `{id}` must be a return value of [`{id}_new`] that [`{id}_drop`] has not yet been called on.
            ///
            /// # Panics
            ///
            /// - If `min_bound > max_bound`.
            /// - If the encoding ran out of memory
            #[no_mangle]
            pub unsafe extern "C" fn {id}_encode_lb(
                {id}: *mut {enc},
                min_bound: usize,
                max_bound: usize,
                n_vars_used: &mut u32,
                collector: CClauseCollector,
                collector_data: *mut c_void,
            ) {{
                assert!(min_bound <= max_bound);
                let mut collector = ClauseCollector::new(collector, collector_data);
                let mut var_manager = VarManager::new(n_vars_used);
                (*{id})
                    .encode_lb_change(min_bound..=max_bound, &mut collector, &mut var_manager)
                    .expect("clause collector returned out of memory");
            }}
            "#
        )?;
        writeln!(
            writer,
            r#"
            /// Returns an assumption/unit for enforcing a lower bound (`sum of lits >= lb`). Make sure that
            /// [`{id}_encode_lb`] has been called adequately and nothing has been called afterwards, otherwise
            /// [`MaybeError::NotEncoded`] will be returned.
            ///
            /// # Safety
            ///
            /// `{id}` must be a return value of [`{id}_new`] that [`{id}_drop`] has not yet been called on.
            #[no_mangle]
            pub unsafe extern "C" fn {id}_enforce_lb(
                {id}: *mut {enc},
                ub: usize,
                assump: &mut c_int,
            ) -> MaybeError {{
                match (*{id}).enforce_lb(ub) {{
                    Ok(assumps) => {{
                        debug_assert_eq!(assumps.len(), 1);
                        *assump = assumps[0].to_ipasir();
                        MaybeError::Ok
                    }}
                    Err(err) => err.into(),
                }}
            }}
            "#
        )?;
    }
    Ok(())
}
