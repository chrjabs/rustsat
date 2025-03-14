#!/usr/bin/env bash

VERSION=$(grep '^version = "[[:digit:]]\+.[[:digit:]]\+.[[:digit:]]\+"' Cargo.toml | cut -d '"' -f2)
MAJOR=$(echo "${VERSION}" | cut -d '.' -f1)
MINOR=$(echo "${VERSION}" | cut -d '.' -f2)
PATCH=$(echo "${VERSION}" | cut -d '.' -f3)

sed -i -E \
  -e "s/^#define RUSTSAT_VERSION [[:digit:]]+.[[:digit:]]+.[[:digit:]]+$/#define RUSTSAT_VERSION ${MAJOR}.${MINOR}.${PATCH}/g" \
  -e "s/^#define RUSTSAT_VERSION_MAJOR [[:digit:]]+$/#define RUSTSAT_VERSION_MAJOR ${MAJOR}/g" \
  -e "s/^#define RUSTSAT_VERSION_MINOR [[:digit:]]+$/#define RUSTSAT_VERSION_MINOR ${MINOR}/g" \
  -e "s/^#define RUSTSAT_VERSION_PATCH [[:digit:]]+$/#define RUSTSAT_VERSION_PATCH ${PATCH}/g" \
  capi/rustsat.h
