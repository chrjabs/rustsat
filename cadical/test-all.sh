#!/usr/bin/env bash

echo "Testing default (newest) version"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test &> def-test.log
echo "Default (newest) test returned: $?"

echo "Testing v1.5.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-5-0 &> v150-test.log
echo "v1.5.0 test returned: $?"

echo "Testing v1.5.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-5-1 &> v151-test.log
echo "v1.5.1 test returned: $?"

echo "Testing v1.5.2"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-5-2 &> v152-test.log
echo "v1.5.2 test returned: $?"

echo "Testing v1.5.3"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-5-3 &> v153-test.log
echo "v1.5.3 test returned: $?"

echo "Testing v1.5.4"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-5-4 &> v154-test.log
echo "v1.5.4 test returned: $?"

echo "Testing v1.5.5"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-5-5 &> v155-test.log
echo "v1.5.5 test returned: $?"

echo "Testing v1.5.6"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-5-6 &> v156-test.log
echo "v1.5.6 test returned: $?"

echo "Testing v1.6.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-6-0 &> v160-test.log
echo "v1.6.0 test returned: $?"

echo "Testing v1.7.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-7-0 &> v170-test.log
echo "v1.7.0 test returned: $?"

echo "Testing v1.7.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-7-1 &> v171-test.log
echo "v1.7.1 test returned: $?"

echo "Testing v1.7.2"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-7-2 &> v172-test.log
echo "v1.7.2 test returned: $?"

echo "Testing v1.7.3"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-7-3 &> v173-test.log
echo "v1.7.3 test returned: $?"

echo "Testing v1.7.4"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-7-4 &> v174-test.log
echo "v1.7.4 test returned: $?"

echo "Testing v1.7.5"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-7-5 &> v175-test.log
echo "v1.7.5 test returned: $?"

echo "Testing v1.8.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-8-0 &> v180-test.log
echo "v1.8.0 test returned: $?"

echo "Testing v1.9.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-9-0 &> v190-test.log
echo "v1.9.0 test returned: $?"

echo "Testing v1.9.1"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-9-1 &> v191-test.log
echo "v1.9.1 test returned: $?"

echo "Testing v1.9.2"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-9-2 &> v192-test.log
echo "v1.9.2 test returned: $?"

echo "Testing v1.9.3"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-9-3 &> v193-test.log
echo "v1.9.3 test returned: $?"

echo "Testing v1.9.4"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-9-4 &> v194-test.log
echo "v1.9.4 test returned: $?"

echo "Testing v1.9.5"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v1-9-5 &> v195-test.log
echo "v1.9.5 test returned: $?"

echo "Testing v2.0.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v2-0-0 &> v200-test.log
echo "v2.0.0 test returned: $?"

echo "Testing v2.1.0"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=v2-1-0 &> v210-test.log
echo "v2.1.0 test returned: $?"

echo "Testing quiet"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=quiet &> quiet-test.log
echo "quiet test returned: $?"

echo "Testing logging"
if [ "$1" == "--clean" ]; then cargo clean -p rustsat-cadical > /dev/null; fi
cargo test --features=logging &> logging-test.log
echo "logging test returned: $?"
