#!/usr/bin/bash

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

echo "Building quiet"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=quiet &> quiet-build.log
echo "quiet build returned: $?"

echo "Building safe"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=safe &> safe-build.log
echo "safe build returned: $?"

echo "Building logging"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo build --features=logging &> logging-build.log
echo "logging build returned: $?"
