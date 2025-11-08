"""
Lost-success differential analysis module.

Analyzes the 96 lemmas that are verified in Baseline-RAG but not in Fast/Synergy.
Implements Tasks 8-12 from the analysis specification.
"""

import csv
import json
import random
from pathlib import Path
from typing import Dict, List, Any, Tuple, Set
from collections import defaultdict, Counter
from dataclasses import dataclass, asdict
from loguru import logger
import difflib


@dataclass
class LostLemmaRecord:
    """Record for a lost-success lemma."""
    lemma_id: str
    category: str
    complexity_band: str

    baseline_status: str
    fast_status: str
    synergy_status: str

    baseline_runtime: float
    fast_runtime: float
    synergy_runtime: float

    fast_failure_mode: str
    synergy_failure_mode: str

    change_type_fast: str  # NO_CHANGE/SHALLOW_CHANGE/STRUCTURAL_CHANGE
    change_type_synergy: str
    change_score_fast: float  # Diff score
    change_score_synergy: float

    orig_stmt: str
    fast_stmt: str
    synergy_stmt: str

    baseline_error: str
    fast_error: str
    synergy_error: str


# ============================================================================
# Task 8: Isolate Lost Success Lemmas
# ============================================================================

def isolate_lost_successes(joint_table: Dict[str, Any]) -> List[str]:
    """
    Identify lemmas verified in Baseline-RAG but not in Fast/Synergy.

    Args:
        joint_table: Joint results table

    Returns:
        List of lost lemma IDs
    """
    lost = []

    for lemma_id, record in joint_table.items():
        baseline_verified = record.baseline_status == "Verified"
        fast_not_verified = record.fast_status != "Verified"

        if baseline_verified and fast_not_verified:
            lost.append(lemma_id)

    logger.info(f"Found {len(lost)} lost success lemmas")
    return lost


def save_lost_successes(
    joint_table: Dict[str, Any],
    lost_ids: List[str],
    output_csv: Path
) -> None:
    """
    Save lost successes to CSV.

    Args:
        joint_table: Joint results table
        lost_ids: List of lost lemma IDs
        output_csv: Output CSV path
    """
    output_csv.parent.mkdir(parents=True, exist_ok=True)

    with open(output_csv, 'w', newline='') as f:
        fieldnames = [
            'lemma_id', 'category', 'complexity_band',
            'baseline_status', 'fast_status', 'synergy_status',
            'baseline_runtime', 'fast_runtime', 'synergy_runtime',
            'baseline_error', 'fast_error', 'synergy_error'
        ]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()

        for lemma_id in lost_ids:
            record = joint_table[lemma_id]
            row = {
                'lemma_id': lemma_id,
                'category': record.category,
                'complexity_band': record.complexity_band,
                'baseline_status': record.baseline_status,
                'fast_status': record.fast_status,
                'synergy_status': record.synergy_status,
                'baseline_runtime': record.baseline_runtime,
                'fast_runtime': record.fast_runtime,
                'synergy_runtime': record.synergy_runtime,
                'baseline_error': record.baseline_error,
                'fast_error': record.fast_error,
                'synergy_error': record.synergy_error
            }
            writer.writerow(row)

    logger.info(f"Saved lost successes to {output_csv}")


def summarize_lost_successes(
    joint_table: Dict[str, Any],
    lost_ids: List[str],
    output_json: Path
) -> Dict[str, int]:
    """
    Generate summary statistics for lost successes.

    Args:
        joint_table: Joint results table
        lost_ids: List of lost lemma IDs
        output_json: Output JSON path

    Returns:
        Summary dictionary
    """
    summary = {
        'total_lost': len(lost_ids),
        'failed_in_fast': 0,
        'abstained_in_fast': 0,
        'error_in_fast': 0,
        'timeout_in_fast': 0,
        'failed_in_synergy': 0,
        'abstained_in_synergy': 0,
        'error_in_synergy': 0,
        'timeout_in_synergy': 0
    }

    for lemma_id in lost_ids:
        record = joint_table[lemma_id]

        # Fast status
        if record.fast_status == "Failed":
            summary['failed_in_fast'] += 1
        elif record.fast_status == "Abstained":
            summary['abstained_in_fast'] += 1
        elif record.fast_status == "Error":
            summary['error_in_fast'] += 1

        # Synergy status
        if record.synergy_status == "Failed":
            summary['failed_in_synergy'] += 1
        elif record.synergy_status == "Abstained":
            summary['abstained_in_synergy'] += 1
        elif record.synergy_status == "Error":
            summary['error_in_synergy'] += 1

    # Save to JSON
    output_json.parent.mkdir(parents=True, exist_ok=True)
    with open(output_json, 'w') as f:
        json.dump(summary, f, indent=2)

    logger.info(f"Saved lost successes summary to {output_json}")
    return summary


# ============================================================================
# Task 9: Compare Original vs Sanitized Statements
# ============================================================================

def compute_diff_score(stmt1: str, stmt2: str) -> float:
    """
    Compute token-based diff score between two Coq statements.

    Args:
        stmt1: First statement
        stmt2: Second statement

    Returns:
        Diff score (0.0 = identical, 1.0 = completely different)
    """
    # Tokenize by whitespace
    tokens1 = stmt1.split()
    tokens2 = stmt2.split()

    # Use SequenceMatcher for ratio
    matcher = difflib.SequenceMatcher(None, tokens1, tokens2)
    similarity = matcher.ratio()

    return 1.0 - similarity


def classify_change_type(diff_score: float) -> str:
    """
    Classify change type based on diff score.

    Args:
        diff_score: Diff score

    Returns:
        "NO_CHANGE", "SHALLOW_CHANGE", or "STRUCTURAL_CHANGE"
    """
    if diff_score < 0.01:
        return "NO_CHANGE"
    elif diff_score < 0.3:
        return "SHALLOW_CHANGE"
    else:
        return "STRUCTURAL_CHANGE"


def annotate_statement_diffs(
    joint_table: Dict[str, Any],
    lost_ids: List[str]
) -> None:
    """
    Annotate lost lemmas with statement diff information.

    NOTE: This is a placeholder since we don't have access to final ASTs
    in the current data format. In a real implementation, this would need
    to extract final_ast from additional logs or state files.

    Args:
        joint_table: Joint results table (modified in place)
        lost_ids: List of lost lemma IDs
    """
    logger.warning("Statement diff annotation not fully implemented - "
                   "final ASTs not available in current data format")

    # Placeholder: just mark everything as SHALLOW_CHANGE
    for lemma_id in lost_ids:
        record = joint_table[lemma_id]
        record.change_type_fast = "SHALLOW_CHANGE"
        record.change_type_synergy = "SHALLOW_CHANGE"
        record.change_score_fast = 0.15
        record.change_score_synergy = 0.15


# ============================================================================
# Task 10: Failure Mode Breakdown
# ============================================================================

def categorize_failure_mode(status: str, error_msg: str) -> str:
    """
    Categorize failure mode from status and error message.

    Args:
        status: Status string (Verified/Failed/Abstained/Error)
        error_msg: Error message

    Returns:
        Failure mode category
    """
    if status == "Verified":
        return "VERIFIED"
    elif status == "Abstained":
        return "GUARD_REJECTED"

    error_lower = error_msg.lower()

    # Type errors
    if any(kw in error_lower for kw in ['type error', 'ill-typed', 'expected type']):
        return "TYPE_ERROR"

    # Unresolved identifiers
    if any(kw in error_lower for kw in ['unbound', 'not found', 'undefined']):
        return "UNRESOLVED_IDENTIFIER"

    # Tactic failures
    if any(kw in error_lower for kw in ['tactic', 'proof', 'hammer', 'auto failed']):
        return "TAC_FAIL"

    # Timeout
    if 'timeout' in error_lower:
        return "TIMEOUT"

    # Default
    return "OTHER"


def analyze_failure_modes(
    joint_table: Dict[str, Any],
    lost_ids: List[str],
    output_dir: Path
) -> None:
    """
    Analyze failure modes for lost lemmas.

    Args:
        joint_table: Joint results table
        lost_ids: List of lost lemma IDs
        output_dir: Output directory
    """
    logger.info("Analyzing failure modes for lost lemmas...")

    # Collect failure modes
    fast_modes = Counter()
    synergy_modes = Counter()

    records = []

    for lemma_id in lost_ids:
        record = joint_table[lemma_id]

        fast_mode = categorize_failure_mode(record.fast_status, record.fast_error)
        synergy_mode = categorize_failure_mode(record.synergy_status, record.synergy_error)

        fast_modes[fast_mode] += 1
        synergy_modes[synergy_mode] += 1

        records.append({
            'lemma_id': lemma_id,
            'fast_failure_mode': fast_mode,
            'synergy_failure_mode': synergy_mode
        })

    # Save CSV
    csv_path = output_dir / "lost_failure_modes.csv"
    with open(csv_path, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=['lemma_id', 'fast_failure_mode', 'synergy_failure_mode'])
        writer.writeheader()
        for r in records:
            writer.writerow(r)

    logger.info(f"Saved failure modes to {csv_path}")

    # Generate LaTeX table
    latex_dir = output_dir / "latex"
    latex_dir.mkdir(exist_ok=True)
    latex_path = latex_dir / "lost_failure_modes.tex"

    with open(latex_path, 'w') as f:
        f.write("\\begin{tabular}{lrr}\n")
        f.write("\\toprule\n")
        f.write("Failure mode & Fast (count) & Synergy (count) \\\\\n")
        f.write("\\midrule\n")

        all_modes = sorted(set(fast_modes.keys()) | set(synergy_modes.keys()))

        for mode in all_modes:
            fast_count = fast_modes.get(mode, 0)
            synergy_count = synergy_modes.get(mode, 0)
            f.write(f"{mode} & {fast_count} & {synergy_count} \\\\\n")

        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")

    logger.info(f"Saved LaTeX failure modes table to {latex_path}")


# ============================================================================
# Task 11: Semantic Category and Complexity of Lost Lemmas
# ============================================================================

def analyze_lost_category_complexity(
    joint_table: Dict[str, Any],
    lost_ids: List[str],
    output_csv: Path
) -> None:
    """
    Analyze semantic category and complexity distribution of lost lemmas.

    Args:
        joint_table: Joint results table
        lost_ids: List of lost lemma IDs
        output_csv: Output CSV path
    """
    logger.info("Analyzing category and complexity of lost lemmas...")

    # Count by category
    category_counts = Counter()
    complexity_counts = Counter()

    for lemma_id in lost_ids:
        record = joint_table[lemma_id]
        category_counts[record.category] += 1
        complexity_counts[record.complexity_band] += 1

    total = len(lost_ids)

    # Build result rows
    rows = []

    # Category breakdown
    for category, count in sorted(category_counts.items()):
        ratio = count / total if total > 0 else 0.0
        rows.append({
            'dimension': 'Category',
            'value': category,
            'count': count,
            'ratio': f"{ratio:.2%}"
        })

    # Complexity breakdown
    for band in ["shallow", "medium", "deep"]:
        count = complexity_counts.get(band, 0)
        ratio = count / total if total > 0 else 0.0
        rows.append({
            'dimension': 'Complexity',
            'value': band,
            'count': count,
            'ratio': f"{ratio:.2%}"
        })

    # Save CSV
    output_csv.parent.mkdir(parents=True, exist_ok=True)
    with open(output_csv, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=['dimension', 'value', 'count', 'ratio'])
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    logger.info(f"Saved lost category/complexity analysis to {output_csv}")


# ============================================================================
# Task 12: Build Lost Lemma Casebook
# ============================================================================

def build_lost_casebook(
    joint_table: Dict[str, Any],
    lost_ids: List[str],
    output_md: Path,
    num_examples: int = 5
) -> None:
    """
    Build a casebook of concrete lost-success examples for the paper.

    Samples diverse examples covering different failure modes.

    Args:
        joint_table: Joint results table
        lost_ids: List of lost lemma IDs
        output_md: Output markdown path
        num_examples: Number of examples to include
    """
    logger.info(f"Building lost lemma casebook with {num_examples} examples...")

    # Group by failure mode
    by_mode = defaultdict(list)
    for lemma_id in lost_ids:
        record = joint_table[lemma_id]
        mode = categorize_failure_mode(record.fast_status, record.fast_error)
        by_mode[mode].append(lemma_id)

    # Sample diverse examples
    examples = []

    # Try to get at least one from each failure mode
    for mode in ["TYPE_ERROR", "UNRESOLVED_IDENTIFIER", "TAC_FAIL", "GUARD_REJECTED", "OTHER"]:
        candidates = by_mode.get(mode, [])
        if candidates and len(examples) < num_examples:
            example_id = random.choice(candidates)
            examples.append(example_id)

    # Fill remaining slots randomly
    while len(examples) < num_examples and len(lost_ids) > len(examples):
        candidate = random.choice(lost_ids)
        if candidate not in examples:
            examples.append(candidate)

    # Write casebook
    output_md.parent.mkdir(parents=True, exist_ok=True)

    with open(output_md, 'w') as f:
        f.write("# Lost Lemma Casebook\n\n")
        f.write(f"Sampled {len(examples)} diverse examples from {len(lost_ids)} lost successes.\n\n")
        f.write("---\n\n")

        for i, lemma_id in enumerate(examples, 1):
            record = joint_table[lemma_id]

            f.write(f"## Example {i}: {lemma_id}\n\n")
            f.write(f"**Category**: {record.category}  \n")
            f.write(f"**Complexity**: {record.complexity_band}  \n\n")

            f.write("### Status Summary\n\n")
            f.write(f"- **Baseline-RAG**: {record.baseline_status} ({record.baseline_runtime:.1f}ms)\n")
            f.write(f"- **SAPSE-Fast**: {record.fast_status} ({record.fast_runtime:.1f}ms)\n")
            f.write(f"- **SAPSE-Synergy**: {record.synergy_status} ({record.synergy_runtime:.1f}ms)\n\n")

            f.write("### Failure Modes\n\n")

            fast_mode = categorize_failure_mode(record.fast_status, record.fast_error)
            synergy_mode = categorize_failure_mode(record.synergy_status, record.synergy_error)

            f.write(f"- **Fast**: {fast_mode}\n")
            f.write(f"- **Synergy**: {synergy_mode}\n\n")

            f.write("### Error Messages\n\n")

            if record.baseline_error:
                f.write(f"**Baseline**: (should not have error, but got) {record.baseline_error[:200]}\n\n")

            if record.fast_error:
                f.write(f"**Fast**: {record.fast_error[:200]}\n\n")

            if record.synergy_error:
                f.write(f"**Synergy**: {record.synergy_error[:200]}\n\n")

            f.write("### Lemma Statement (first 300 chars)\n\n")
            f.write("```coq\n")
            f.write(record.raw_ast[:300])
            f.write("\n```\n\n")

            f.write("---\n\n")

    logger.info(f"Saved lost lemma casebook to {output_md}")


# ============================================================================
# Main Lost-Success Analysis Orchestration
# ============================================================================

def run_lost_success_analysis(
    joint_table: Dict[str, Any],
    output_dir: Path
) -> None:
    """
    Run complete lost-success differential analysis.

    Args:
        joint_table: Joint results table
        output_dir: Output directory
    """
    logger.info("=" * 60)
    logger.info("PART II: Lost-Success Differential Analysis")
    logger.info("=" * 60)

    # Task 8: Isolate lost successes
    lost_ids = isolate_lost_successes(joint_table)
    save_lost_successes(joint_table, lost_ids, output_dir / "lost_successes.csv")
    summary = summarize_lost_successes(joint_table, lost_ids, output_dir / "lost_successes_summary.json")

    logger.info("Lost successes summary:")
    for key, value in summary.items():
        logger.info(f"  {key}: {value}")

    # Task 9: Statement diffs
    annotate_statement_diffs(joint_table, lost_ids)

    # Task 10: Failure modes
    analyze_failure_modes(joint_table, lost_ids, output_dir)

    # Task 11: Category and complexity
    analyze_lost_category_complexity(joint_table, lost_ids, output_dir / "lost_category_complexity.csv")

    # Task 12: Casebook
    build_lost_casebook(joint_table, lost_ids, output_dir / "lost_casebook.md", num_examples=10)

    logger.info("Lost-success analysis complete!")
