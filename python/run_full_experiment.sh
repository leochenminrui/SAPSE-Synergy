#!/bin/bash
#
# SAPSE-Synergy Full Experiment Runner
# Reproduces all 4 configurations on 2K dataset
#
# Usage: bash run_full_experiment.sh [--limit N]
#

set -e

# Parse arguments
LIMIT=""
if [ "$1" == "--limit" ] && [ -n "$2" ]; then
    LIMIT="--limit $2"
    echo "Running with limit: $2 items (for testing)"
fi

# Check environment
echo "==================================================="
echo "SAPSE-Synergy Experiment Runner"
echo "==================================================="
echo ""

# Check Python
if ! command -v python3 &> /dev/null; then
    echo "Error: python3 not found"
    exit 1
fi

PYTHON_VERSION=$(python3 -c 'import sys; print(".".join(map(str, sys.version_info[:2])))')
echo "✓ Python version: $PYTHON_VERSION"

if ! python3 -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)'; then
    echo "Error: Python >= 3.10 required"
    exit 1
fi

# Check Coq
if ! command -v coqc &> /dev/null; then
    echo "⚠ Warning: coqc not found (verification will use mock)"
else
    COQ_VERSION=$(coqc --version | head -1)
    echo "✓ Coq version: $COQ_VERSION"
fi

# Check API key
if [ -z "$DEEPSEEK_API_KEY" ]; then
    echo ""
    echo "⚠ Warning: DEEPSEEK_API_KEY not set"
    echo "   The experiment uses pre-generated lemmas from data/input/"
    echo "   To regenerate lemmas, set DEEPSEEK_API_KEY"
fi

echo ""
echo "==================================================="
echo "Running 4-Configuration Experiment"
echo "==================================================="
echo ""

# Run experiment
python3 scripts/run_synergy_experiments.py \
    --input ../data/input/synergy_rag_2k.jsonl \
    --output-dir ../outputs/reproduction_run \
    $LIMIT

echo ""
echo "==================================================="
echo "Running Analysis"
echo "==================================================="
echo ""

python3 scripts/analyze_synergy_experiments.py \
    --experiment ../outputs/reproduction_run \
    --output-dir ../outputs/analysis_reproduction \
    --all

echo ""
echo "==================================================="
echo "✓ Experiment Complete"
echo "==================================================="
echo ""
echo "Results:"
echo "  - Full results: outputs/reproduction_run/results.csv"
echo "  - Aggregated: outputs/reproduction_run/aggregated_table.md"
echo "  - Analysis: outputs/analysis_reproduction/"
echo ""
echo "To compare with paper numbers:"
echo "  cat outputs/reproduction_run/aggregated_table.md"
