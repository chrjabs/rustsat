#!/usr/bin/env bash

set -eo pipefail

if [ -z "$CARGO" ]; then
  CARGO=$(which cargo)
fi

CAPI_LIB_PATH=$($CARGO build -p rustsat-capi --profile test --message-format=json | jq -r 'select(.target.name == "rustsat_capi").filenames[0]')
CAPI_LIB_DIR=$(dirname "$CAPI_LIB_PATH")
export RUSTFLAGS="--print=native-static-libs"
NATIVE_STATIC_LIBS=$($CARGO build -p rustsat-capi --profile test --message-format=json | jq -r 'select(.reason == "compiler-message").message.message' | grep -E '^native-static-libs:' | sed 's/^native-static-libs: //')

if [ -z "$NEXTEST_ENV" ]; then
  echo "CAPI_LIB_PATH=$CAPI_LIB_PATH"
  echo "CAPI_LIB_DIR=$CAPI_LIB_DIR"
  echo "NATIVE_STATIC_LIBS=$NATIVE_STATIC_LIBS"
  exit 0
fi

{
  echo "CAPI_LIB_PATH=$CAPI_LIB_PATH"
  echo "CAPI_LIB_DIR=$CAPI_LIB_DIR"
  echo "NATIVE_STATIC_LIBS=$NATIVE_STATIC_LIBS"
} >>"$NEXTEST_ENV"
