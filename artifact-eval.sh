#! /usr/bin/env bash
#
# Single-entry evaluation script for the artifact of
#   "KEM-IND-CCA-Preserving Compilation of Jasmin's ML-KEM".
#
# It enters the Nix environment defined by default.nix, removes previous
# build results, checks the Rocq proofs, builds the OCaml compiler from the
# extracted code, runs the compiler test suite, and prints one line per step.
#
# Usage: ./artifact-eval.sh [-j N] [--no-nix] [--no-clean]
#   -j N        parallel jobs for the proofs and the tests (default: 4)
#   --no-nix    do not enter nix-shell (dependencies installed via opam)
#   --no-clean  reuse previous build results instead of rebuilding everything
#
# Logs are written to artifact-eval-logs/.

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SELF="$ROOT/$(basename "${BASH_SOURCE[0]}")"

JOBS=4
USE_NIX=1
CLEAN=1

ARGS=("$@")
while [ $# -gt 0 ]; do
  case "$1" in
    -j) JOBS="$2"; shift 2 ;;
    -j*) JOBS="${1#-j}"; shift ;;
    --no-nix) USE_NIX=0; shift ;;
    --no-clean) CLEAN=0; shift ;;
    -h|--help) sed -n '2,16p' "$SELF" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown option: $1" >&2; exit 1 ;;
  esac
done

# Enter the Nix environment by re-executing this script inside it.
if [ "$USE_NIX" = 1 ] && [ -z "${ARTIFACT_EVAL_IN_NIX:-}" ]; then
  if ! command -v nix-shell > /dev/null; then
    echo "nix-shell not found: install Nix or rerun with --no-nix" >&2
    exit 1
  fi
  echo "Entering nix-shell (the first run downloads/builds the dependencies)"
  export ARTIFACT_EVAL_IN_NIX=1
  exec nix-shell "$ROOT/default.nix" --run "$(printf '%q ' "$SELF" "${ARGS[@]}")"
fi

cd "$ROOT" || exit 1

LOGDIR="$ROOT/artifact-eval-logs"
rm -rf "$LOGDIR"
mkdir -p "$LOGDIR"

# Rocq 9 deprecates COQPATH (set by nix) in favor of ROCQPATH.
if [ -n "${COQPATH:-}" ] && [ -z "${ROCQPATH:-}" ]; then
  export ROCQPATH="$COQPATH"
  unset COQPATH
fi

if [ "$CLEAN" = 1 ]; then
  if ! { make -C proofs clean && make -C compiler clean; } > "$LOGDIR/clean.log" 2>&1; then
    echo "Cleaning failed (see artifact-eval-logs/clean.log)"
    exit 1
  fi
  echo "Removed previous build results"
fi

build_proofs() {
  make -C proofs -j "$JOBS" || return 1
  ! grep -q '^Error' "$LOGDIR/proofs.log"
}

build_compiler() {
  make -C compiler CIL && make -C compiler all
}

run_tests() {
  make -C compiler check JSJOBS="$JOBS"
}

# run_step LABEL LOG COMMAND: print LABEL, run COMMAND logging to LOG, and
# complete the line with the outcome.
FAILED=0
run_step() {
  local label="$1" log="$2"; shift 2
  printf '%-16s ' "$label:"
  if [ "$FAILED" = 1 ]; then
    echo SKIPPED
  elif "$@" > "$log" 2>&1; then
    echo OK
  else
    echo "FAILED (see ${log#"$ROOT"/})"
    FAILED=1
  fi
}

echo "Parallel jobs: $JOBS"
run_step "Rocq proofs" "$LOGDIR/proofs.log" build_proofs
run_step "OCaml compiler" "$LOGDIR/compiler.log" build_compiler
run_step "Tests" "$LOGDIR/tests.log" run_tests

[ "$FAILED" = 0 ]
