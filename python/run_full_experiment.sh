#!/usr/bin/env bash
# Evaluate supplied drafts with a real Coq verifier, then analyze the outcomes.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname -- "$SCRIPT_DIR")"
PYTHON_BIN="${PYTHON_BIN:-python3}"
COQC_BIN="${COQC_BIN:-coqc}"
LIMIT_ARGS=()
if [[ $# -gt 0 ]]; then
    if [[ $# -ne 2 || "$1" != "--limit" || ! "$2" =~ ^[1-9][0-9]*$ ]]; then
        echo "Usage: bash python/run_full_experiment.sh [--limit N]" >&2
        exit 2
    fi
    LIMIT_ARGS=(--limit "$2")
fi

command -v "$PYTHON_BIN" >/dev/null
"$PYTHON_BIN" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)'
if ! command -v "$COQC_BIN" >/dev/null; then
    echo "Error: coqc is required for real evaluation; install Rocq and add coqc to PATH." >&2
    exit 1
fi
"$COQC_BIN" --version
export PYTHONPATH="$SCRIPT_DIR${PYTHONPATH:+:$PYTHONPATH}"

"$PYTHON_BIN" "$SCRIPT_DIR/scripts/run_synergy_experiments.py" \
    --input "$REPO_DIR/data/input/synergy_rag_2k.jsonl" \
    --output-dir "$REPO_DIR/outputs/reproduction_run" \
    --coqc-path "$COQC_BIN" \
    --coq-random-seed 5 \
    "${LIMIT_ARGS[@]}"

"$PYTHON_BIN" "$SCRIPT_DIR/scripts/analyze_synergy_experiments.py" \
    --experiment "$REPO_DIR/outputs/reproduction_run" \
    --input "$REPO_DIR/data/input/synergy_rag_2k.jsonl" \
    --output-dir "$REPO_DIR/outputs/analysis_reproduction" \
    --fragment --category --complexity --lost-successes

printf '%s\n' "Results: $REPO_DIR/outputs/reproduction_run/results.csv" \
    "Summary: $REPO_DIR/outputs/reproduction_run/aggregated_table.md" \
    "Analysis: $REPO_DIR/outputs/analysis_reproduction/"
