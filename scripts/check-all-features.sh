#!/usr/bin/env bash

clean=false
fail=true
none=false
exclude=('default')
package="rustsat"
command="cargo check"
verbose=false
filter=".*"

while [[ $# -gt 0 ]]; do
  case $1 in
    -c|--clean)
      clean=true
      ;;

    --no-fail-fast)
      fail=false
      ;;

    -f|--filter)
      shift
      filter=$1
      ;;

    -e|--exclude)
      shift
      exclude+=($1)
      ;;

    -n|--none)
      none=true
      ;;

    -b|--build)
      command="cargo build"
      ;;

    -t|--test)
      command="cargo nextest run"
      ;;

    -p|--package)
      shift
      package=$1
      ;;

    -v|--verbose)
      verbose=true
      ;;

    --)
      shift
      break
      ;;

    *)
      echo 2>&1 "using command: $1"
      command=$1
      ;;
  esac
  shift
done

args="$@"

if $verbose; then
  echo 2>&1 "clean=$clean"
  echo 2>&1 "fail=$fail"
  echo 2>&1 "none=$none"
  echo 2>&1 "exclude=$exclude"
  echo 2>&1 "package=$package"
  echo 2>&1 "command=$command"
  echo 2>&1 "filter=$filter"
  echo 2>&1
fi

outdir="target/check-all-features-$package"
mkdir -p "$outdir"

ret=0

function run {
  if $clean; then cargo clean -p $package > /dev/null; fi
  features=""
  id=""
  for f in "$@"; do
    features="$features --features=$f"
    id="$id-$f"
  done
  if [ -n $args ]; then
    id="$id-${args// /-}"
  fi
  ofile="$outdir/${command// /-}$id.log"
  cmd="$command -p $package --no-default-features$features $args"
  echo "running: $cmd"
  $cmd &> "$ofile"
  r=$?
  if [[ $r -ne 0 ]]; then
    echo "$ofile"
    echo "====="
    cat "$ofile"
    echo "====="
  fi
  if $fail && [[ $r -ne 0 ]]; then
    exit $r
  fi
  ret=$((ret+r))
}

# run without any features
if $none; then
  run
fi

# iterate over all features
for f in $(cargo metadata --format-version=1 --no-deps | jq ".packages[] | select(.name==\"$package\") | .features | keys[]"); do
  f=$(echo $f | tr -d '"')
  if ! echo "$f" | grep -q "$filter" > /dev/null; then
    echo "skipping feature: $f"
    continue
  fi
  if [[ "${exclude[@]}" =~ "$f" ]]; then
    echo "skipping feature: $f"
    continue
  fi
  run $f
done

exit $ret
