#!/usr/bin/env bash

PACKAGES=$(cargo metadata --no-deps --format-version=1 | jq -r '.packages[].name')
EXCLUDE="rustsat-capi rustsat-pyapi"

for PKG in ${PACKAGES}; do
  if ! echo ${EXCLUDE} | grep -q -P "( |^)${PKG}( |$)"; then
    cargo publish -p ${PKG} --dry-run --verbose "$@" || exit $?
  fi
done
