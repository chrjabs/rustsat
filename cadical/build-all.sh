#!/usr/bin/env bash

echo "Building default (newest) version"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build &> def-build.log
echo "Default (newest) build returned: $?"

echo "Building v1.5.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-5-0 &> v150-build.log
echo "v1.5.0 build returned: $?"

echo "Building v1.5.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-5-1 &> v151-build.log
echo "v1.5.1 build returned: $?"

echo "Building v1.5.2"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-5-2 &> v152-build.log
echo "v1.5.2 build returned: $?"

echo "Building v1.5.3"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-5-3 &> v153-build.log
echo "v1.5.3 build returned: $?"

echo "Building v1.5.4"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-5-4 &> v154-build.log
echo "v1.5.4 build returned: $?"

echo "Building v1.5.5"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-5-5 &> v155-build.log
echo "v1.5.5 build returned: $?"

echo "Building v1.5.6"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-5-6 &> v156-build.log
echo "v1.5.6 build returned: $?"

echo "Building v1.6.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-6-0 &> v160-build.log
echo "v1.6.0 build returned: $?"

echo "Building v1.7.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-7-0 &> v170-build.log
echo "v1.7.0 build returned: $?"

echo "Building v1.7.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-7-1 &> v171-build.log
echo "v1.7.1 build returned: $?"

echo "Building v1.7.2"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-7-2 &> v172-build.log
echo "v1.7.2 build returned: $?"

echo "Building v1.7.3"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-7-3 &> v173-build.log
echo "v1.7.3 build returned: $?"

echo "Building v1.7.4"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-7-4 &> v174-build.log
echo "v1.7.4 build returned: $?"

echo "Building v1.7.5"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-7-5 &> v175-build.log
echo "v1.7.5 build returned: $?"

echo "Building v1.8.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-8-0 &> v180-build.log
echo "v1.8.0 build returned: $?"

echo "Building v1.9.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-9-0 &> v190-build.log
echo "v1.9.0 build returned: $?"

echo "Building v1.9.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-9-1 &> v191-build.log
echo "v1.9.1 build returned: $?"

echo "Building v1.9.2"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-9-2 &> v192-build.log
echo "v1.9.2 build returned: $?"

echo "Building v1.9.3"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-9-3 &> v193-build.log
echo "v1.9.3 build returned: $?"

echo "Building v1.9.4"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-9-4 &> v194-build.log
echo "v1.9.4 build returned: $?"

echo "Building v1.9.5"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v1-9-5 &> v195-build.log
echo "v1.9.5 build returned: $?"

echo "Building v2.0.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v2-0-0 &> v200-build.log
echo "v2.0.0 build returned: $?"

echo "Building v2.1.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=v2-1-0 &> v210-build.log
echo "v2.1.0 build returned: $?"

echo "Building quiet"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=quiet &> quiet-build.log
echo "quiet build returned: $?"

echo "Building logging"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=logging &> logging-build.log
echo "logging build returned: $?"
