#!/usr/bin/env bash

echo "Testing default (newest) version"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test &> def-test.log
echo "Default (newest) test returned: $?"

echo "Testing sc2022-bulky"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=sc2022-bulky &> sc2022-bulky-test.log
echo "sc2022-bulky test returned: $?"

echo "Testing sc2022-hyper"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=sc2022-hyper &> sc2022-hyper-test.log
echo "sc2022-hyper test returned: $?"

echo "Testing sc2022-light"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=sc2022-light &> sc2022-light-test.log
echo "sc2022-light test returned: $?"

echo "Testing v3.0.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=v3-0-0 &> v300-test.log
echo "v3.0.0 test returned: $?"

echo "Testing v3.1.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=v3-1-0 &> v310-test.log
echo "v3.1.0 test returned: $?"

echo "Testing v3.1.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=v3-1-1 &> v311-test.log
echo "v3.1.1 test returned: $?"

echo "Testing v4.0.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=v4-0-0 &> v400-test.log
echo "v4.0.0 test returned: $?"

echo "Testing v4.0.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=v4-0-1 &> v401-test.log
echo "v4.0.1 test returned: $?"

echo "Testing v4.0.2"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=v4-0-2 &> v402-test.log
echo "v4.0.2 test returned: $?"

echo "Testing quiet"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=quiet &> quiet-test.log
echo "quiet test returned: $?"

echo "Testing safe"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo test --features=safe &> safe-test.log
echo "safe test returned: $?"
