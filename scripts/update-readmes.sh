#!/usr/bin/env bash

cargo rdme
for dir in tools cadical kissat minisat glucose batsat ipasir capi pyapi pigeons; do
  cd "${dir}"
  cargo rdme
  cd ..
done
