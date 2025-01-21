#!/usr/bin/env bash

echo "Building default (newest) version"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build &> def-build.log
echo "Default (newest) build returned: $?"

echo "Building sc2022-bulky"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=sc2022-bulky &> sc2022-bulky-build.log
echo "sc2022-bulky build returned: $?"

echo "Building sc2022-hyper"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=sc2022-hyper &> sc2022-hyper-build.log
echo "sc2022-hyper build returned: $?"

echo "Building sc2022-light"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=sc2022-light &> sc2022-light-build.log
echo "sc2022-light build returned: $?"

echo "Building v3.0.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=v3-0-0 &> v300-build.log
echo "v3.0.0 build returned: $?"

echo "Building v3.1.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=v3-1-0 &> v310-build.log
echo "v3.1.0 build returned: $?"

echo "Building v3.1.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=v3-1-1 &> v311-build.log
echo "v3.1.1 build returned: $?"

echo "Building v4.0.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=v4-0-0 &> v400-build.log
echo "v4.0.0 build returned: $?"

echo "Building v4.0.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=v4-0-1 &> v401-build.log
echo "v4.0.1 build returned: $?"

echo "Building quiet"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=quiet &> quiet-build.log
echo "quiet build returned: $?"

echo "Building safe"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-kissat > /dev/null; fi
cargo build --features=safe &> safe-build.log
echo "safe build returned: $?"
