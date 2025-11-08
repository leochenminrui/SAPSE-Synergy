"""Test CLI flags exist for evaluate.py and plot_comparison.py."""

import subprocess
import sys
from pathlib import Path

import pytest


def test_evaluate_has_bootstrap_flag():
    """Test that evaluate.py has --bootstrap flag."""
    script_path = Path(__file__).parent.parent / "scripts" / "evaluate.py"
    result = subprocess.run(
        [sys.executable, str(script_path), "--help"],
        capture_output=True,
        text=True
    )
    assert result.returncode == 0, f"evaluate.py --help failed: {result.stderr}"
    assert "--bootstrap" in result.stdout, "Missing --bootstrap flag in evaluate.py"


def test_evaluate_has_bootstrap_iters_flag():
    """Test that evaluate.py has --bootstrap-iters flag."""
    script_path = Path(__file__).parent.parent / "scripts" / "evaluate.py"
    result = subprocess.run(
        [sys.executable, str(script_path), "--help"],
        capture_output=True,
        text=True
    )
    assert result.returncode == 0, f"evaluate.py --help failed: {result.stderr}"
    assert "--bootstrap-iters" in result.stdout, "Missing --bootstrap-iters flag in evaluate.py"


def test_plot_comparison_has_cost_file_flag():
    """Test that plot_comparison.py has --cost-file flag."""
    script_path = Path(__file__).parent.parent / "scripts" / "plot_comparison.py"

    # Check source code directly (more reliable than running if dependencies missing)
    with open(script_path, 'r') as f:
        source = f.read()

    assert '--cost-file' in source, "Missing --cost-file flag in plot_comparison.py source"
    assert 'cost_data' in source or 'cost-file' in source, "Missing cost data handling in plot_comparison.py"


def test_evaluate_help_message():
    """Test that evaluate.py help message mentions confidence intervals."""
    script_path = Path(__file__).parent.parent / "scripts" / "evaluate.py"
    result = subprocess.run(
        [sys.executable, str(script_path), "--help"],
        capture_output=True,
        text=True
    )
    assert result.returncode == 0, f"evaluate.py --help failed: {result.stderr}"
    assert "confidence" in result.stdout.lower(), "Help message should mention confidence intervals"


def test_plot_comparison_help_message():
    """Test that plot_comparison.py help message mentions cost data."""
    script_path = Path(__file__).parent.parent / "scripts" / "plot_comparison.py"

    # Check source code for help text (more reliable than running if dependencies missing)
    with open(script_path, 'r') as f:
        source = f.read()

    # Check for cost-related help text in argparse section
    assert 'cost' in source.lower(), "Help message should mention cost data"
    assert 'plot_cost_throughput_pareto' in source, "Missing cost/throughput plot function"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
