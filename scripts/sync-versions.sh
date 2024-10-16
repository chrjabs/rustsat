#!/usr/bin/env bash

VERSION=$(grep '^version = "[[:digit:]]\+.[[:digit:]]\+.[[:digit:]]\+"' Cargo.toml | cut -d '"' -f2)
SED_PATTERN="s/^version = \"[[:digit:]]\+.[[:digit:]]\+.[[:digit:]]\+\"$/version = \"${VERSION}\"/g"

# sync C-API version
sed -e "${SED_PATTERN}" -i capi/Cargo.toml
# sync Python API version
sed -e "${SED_PATTERN}" -i pyapi/Cargo.toml
