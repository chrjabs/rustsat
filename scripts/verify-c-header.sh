#!/usr/bin/env bash

VERSION=$(grep '^version = "[[:digit:]]\+.[[:digit:]]\+.[[:digit:]]\+"' Cargo.toml | cut -d '"' -f2)
MAJOR=$(echo "${VERSION}" | cut -d '.' -f1)
MINOR=$(echo "${VERSION}" | cut -d '.' -f2)
PATCH=$(echo "${VERSION}" | cut -d '.' -f3)

TMP_CONF=$(mktemp XXXXXXXXXX.cbindgen.toml)

sed "s/after_includes = \"\"/after_includes = \"#define RUSTSAT_VERSION ${VERSION}\\\n#define RUSTSAT_VERSION_MAJOR ${MAJOR}\\\n#define RUSTSAT_VERSION_MINOR ${MINOR}\\\n#define RUSTSAT_VERSION_PATCH ${PATCH}\"/g" capi/cbindgen.toml > ${TMP_CONF}

cbindgen -c ${TMP_CONF} --crate rustsat-capi -o capi/rustsat.h --verify
RET=$?

rm ${TMP_CONF}

exit ${RET}
