#!/usr/bin/bash

echo "Testing default (newest) version"
cargo test &> def-test.log
echo "Default (newest) test returned: $?"

echo "Testing v1.5.0"
cargo test --features=v1-5-0 &> v150-test.log
echo "v1.5.0 test returned: $?"

echo "Testing v1.5.1"
cargo test --features=v1-5-1 &> v151-test.log
echo "v1.5.1 test returned: $?"

echo "Testing v1.5.2"
cargo test --features=v1-5-2 &> v152-test.log
echo "v1.5.2 test returned: $?"

echo "Testing v1.5.3"
cargo test --features=v1-5-3 &> v153-test.log
echo "v1.5.3 test returned: $?"

echo "Testing v1.5.4"
cargo test --features=v1-5-4 &> v154-test.log
echo "v1.5.4 test returned: $?"

echo "Testing v1.5.5"
cargo test --features=v1-5-5 &> v155-test.log
echo "v1.5.5 test returned: $?"

echo "Testing v1.5.6"
cargo test --features=v1-5-6 &> v156-test.log
echo "v1.5.6 test returned: $?"

echo "Testing v1.6.0"
cargo test --features=v1-6-0 &> v160-test.log
echo "v1.6.0 test returned: $?"

echo "Testing v1.7.0"
cargo test --features=v1-7-0 &> v170-test.log
echo "v1.7.0 test returned: $?"

echo "Testing v1.7.1"
cargo test --features=v1-7-1 &> v171-test.log
echo "v1.7.1 test returned: $?"

echo "Testing v1.7.2"
cargo test --features=v1-7-2 &> v172-test.log
echo "v1.7.2 test returned: $?"

echo "Testing quiet"
cargo test --features=quiet &> quiet-test.log
echo "quiet test returned: $?"

echo "Testing safe"
cargo test --features=safe &> safe-test.log
echo "safe test returned: $?"

echo "Testing logging"
cargo test --features=logging &> logging-test.log
echo "logging test returned: $?"
