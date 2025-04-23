#!/usr/bin/env bash

if [ -z "$CARGO" ]; then
  CARGO=$(which cargo)
fi

CAPI_LIB_PATH=$($CARGO build -p rustsat-capi --profile test --message-format=json | jq -r 'select(.target.name == "rustsat_capi").filenames[0]')
CAPI_LIB_DIR=$(dirname $CAPI_LIB_PATH)

if [ -z "$NEXTEST_ENV" ]; then
  echo "CAPI_LIB_PATH=$CAPI_LIB_PATH"
  echo "CAPI_LIB_DIR=$CAPI_LIB_DIR"
  exit 0
fi

echo "CAPI_LIB_PATH=$CAPI_LIB_PATH" >> "$NEXTEST_ENV"
echo "CAPI_LIB_DIR=$CAPI_LIB_DIR" >> "$NEXTEST_ENV"
