#!/bin/bash -l
#SBATCH -J rustsat-fuzz:card
#SBATCH -o /wrk-kappa/users/chrisjab/rustsat-fuzz/slurm/card_%a.out
#SBATCH -e /wrk-kappa/users/chrisjab/rustsat-fuzz/slurm/card_%a.err
#SBATCH -t 600
#SBATCH -M kale
#SBATCH -p short
#SBATCH --account=cs_ukko2
#SBATCH --exclusive=user
#SBATCH --mem=50GB
#SBATCH --array=1
#SBATCH --ntasks=24
#SBATCH --cpus-per-task=1
#SBATCH --chdir=/home/chrisjab/sat-rs/rustsat
#SBATCH -x kale-g[904-905]

module purge
module load GCC/10.3.0 zlib/1.2.11-GCCcore-10.3.0 bzip2/1.0.8-GCCcore-10.3.0 CMake/3.20.1-GCCcore-10.3.0 Clang/12.0.1-GCCcore-10.3.0 Gurobi/12.0.1-GCCcore-13.3.0
module list
echo ${LD_LIBRARY_PATH}

FUZZ_TARGET_DIR="/home/chrisjab/sat-rs/rustsat/fuzz/target"
FUZZ_DATA_DIR="/wrk-kappa/users/chrisjab/rustsat-fuzz"

case "$SLURM_ARRAY_TASK_ID" in
  1)
    ENCODING="totalizer"
    ;;
esac

mkdir -p "$FUZZ_DATA_DIR/artifacts/$ENCODING"

export AFL_NO_UI=1
export AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1
export AFL_TESTCACHE_SIZE=500
export AFL_NO_AFFINITY=1
export AFL_IGNORE_SEED_PROBLEMS=1

launch_fuzzer () {
  local BINARY="$1"
  shift
  srun --ntasks=1 -c 1 --exclusive --mem=2GB \
    cargo afl fuzz "$@" \
    -i "$FUZZ_DATA_DIR/corpus/$ENCODING" -o "$FUZZ_DATA_DIR/artifacts/$ENCODING" \
    -- "$BINARY"&
}

export AFL_FINAL_SYNC=1
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -M main -l 2ATR -a binary
unset AFL_FINAL_SYNC

sleep 5s

launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S workerCmplog -a binary

export AFL_USE_ASAN=1
launch_fuzzer "$FUZZ_TARGET_DIR/x86_64-unknown-linux-gnu/sanitizers/$ENCODING" -S workerSan -c - -a binary
unset AFL_USE_ASAN

launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker1 -L0 -p fast -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker2 -Z -p coe -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker3 -p lin -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker4 -p quad -c -
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker5 -p exploit -P exploit -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker6 -p rare -P exploit -c -
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker7 -P explore -c -
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker8 -p fast -P explore -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker9 -p coe -P explore -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker10 -p lin -P explore -c - -a binary

export AFL_DISABLE_TRIM=1

launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker11 -L0 -p quad -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker12 -Z -p exploit -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker13 -p rare -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker14 -c -
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker15 -p fast -P exploit -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker16 -p coe -P exploit -c -
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker17 -p lin -P explore -c -
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker18 -p quad -P explore -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker19 -p exploit -P explore -c - -a binary
launch_fuzzer "$FUZZ_TARGET_DIR/debug/$ENCODING" -S worker20 -p rare -P explore -c - -a binary

wait
