#!/usr/bin/env bash

echo "toolchain=$(grep '^channel = ' rust-toolchain.toml | cut -d '"' -f2)"
echo "msrv=$(grep '^rust-version = ' Cargo.toml | cut -d '"' -f2)"
