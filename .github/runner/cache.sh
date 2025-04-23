#!/usr/bin/env bash

set -euo pipefail

if [ -z "$CACHE" ]; then
  CACHE="/runner/cache"
fi

RUST=false

# Parse command line
while [[ $# -gt 0 ]]; do
  case "$1" in
    restore)
      COMMAND="restore"
      shift
      ;;

    save)
      COMMAND="save"
      shift
      ;;

    --key)
      KEY="$2"
      shift
      shift
      ;;

    --rust)
      RUST=true
      shift
      ;;

    *)
      break
      ;;
  esac
done

CACHE_DIR="$CACHE/$KEY.cache/"

case "$COMMAND" in
  "restore")
    echo "🔎 Checking for matching cache"
    if [ -d "$CACHE_DIR" ]; then
      echo "🔙 Restoring cache from '$CACHE_DIR'"
      rsync --archive --stats --human-readable "$CACHE_DIR" .
      echo "✅ Finished restoring cache"
    else
      echo "❌ No matching cache found"
    fi
    ;;

  "save")
    if $RUST; then
      echo "🧹 Cleaning up target directory"
      cargo metadata --format-version=1 | \
        jq --raw-output '.packages[] | select(.source==null).name' | \
        while read package; do
          cargo clean -p $package
        done
    fi
    echo "💾 Saving cache to '$CACHE_DIR'"
    rsync --archive --delete --stats --human-readable --relative "target/" "$@" "$CACHE_DIR"
    echo "✅ Finished saving cache"
    ;;

  *)
    >&2 echo "Unknown command '$1'"
    exit 1
    ;;
esac
