#!/usr/bin/env python3
"""
Comprehensive analysis script for SAPSE-Synergy 2K experiments.

This script performs differential and extended analysis on the 4-configuration
Synergy benchmark (Baseline-RAG, SAPSE-Strict, SAPSE-Fast, SAPSE-Synergy).

EXPERIMENT SEMANTICS (DO NOT CHANGE):
- Baseline-RAG: No sanitization, direct RAG output
- SAPSE-Strict: Verified core only (VC-guarded)
- SAPSE-Fast: Unverified utility passes only (no guards)
- SAPSE-Synergy: Utility passes → Verified core (UP → VC)

The main 2K experiment is run via scripts/run_synergy_experiments.py.
Results are stored in outputs/synergy_deepseek_real_2k_seed*/.

This analysis script:
1. Builds a joint per-lemma results table aligning all 4 configurations
2. Performs fragment coverage analysis (in-frag vs out-of-frag)
3. Semantic category breakdown (Arithmetic/Boolean/List/Inductive/Misc)
4. Structural complexity analysis (AST depth, binder count)
5. Verified core vs unverified passes comparison (Fast vs Synergy)
6. Extra baseline comparisons (regex sanitizer, CoqHammer-only)
7. Differential analysis of "lost successes" (96 lemmas verified in Baseline but not Fast/Synergy)

Author: Claude (code assistant)
Date: 2025-11-08
"""

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple, Set
from collections import defaultdict, Counter
from dataclasses import dataclass, asdict
from loguru import logger
import hashlib


# ============================================================================
# Data Structures
# ============================================================================

@dataclass
class LemmaRecord:
    """Unified per-lemma record across all configurations."""
    lemma_id: str

    # Per-configuration status (Verified/Failed/Abstained/Error)
    baseline_status: str = ""
    strict_status: str = ""
    fast_status: str = ""
    synergy_status: str = ""

    # Per-configuration runtime (ms)
    baseline_runtime: float = 0.0
    strict_runtime: float = 0.0
    fast_runtime: float = 0.0
    synergy_runtime: float = 0.0

    # Per-configuration URC flags
    baseline_urc: int = 0
    strict_urc: int = 0
    fast_urc: int = 0
    synergy_urc: int = 0

    # Semantic category (to be filled by categorization logic)
    category: str = ""

    # Fragment coverage (to be filled by fragment checker)
    in_frag_baseline: bool = False
    in_frag_strict: bool = False
    in_frag_fast: bool = False
    in_frag_synergy: bool = False

    # Complexity metrics (to be filled by complexity analyzer)
    ast_depth: int = 0
    binder_count: int = 0
    complexity_band: str = ""  # shallow/medium/deep

    # Raw AST and final AST (for lost-success analysis)
    raw_ast: str = ""
    baseline_final_ast: str = ""
    strict_final_ast: str = ""
    fast_final_ast: str = ""
    synergy_final_ast: str = ""

    # Error messages (for failure mode analysis)
    baseline_error: str = ""
    strict_error: str = ""
    fast_error: str = ""
    synergy_error: str = ""

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for CSV export."""
        return asdict(self)


@dataclass
class CategoryStats:
    """Statistics for a semantic category."""
    category: str
    num_lemmas: int
    verified_baseline: int
    verified_strict: int
    verified_fast: int
    verified_synergy: int
    abstained_strict: int
    abstained_synergy: int

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class FragmentCoverageStats:
    """Statistics for fragment coverage analysis."""
    category: str
    num_lemmas: int
    in_frag_count: int
    in_frag_ratio: float
    synergy_verified_in_frag: int
    synergy_verified_out_frag: int

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class ComplexityStats:
    """Statistics for complexity band analysis."""
    band: str
    num_lemmas: int
    verified_baseline: int
    verified_strict: int
    verified_fast: int
    verified_synergy: int
    abstained_strict: int
    abstained_synergy: int

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


# ============================================================================
# Task 7: Build Joint Per-Lemma Results Table
# ============================================================================

def load_synergy_results(results_csv: Path) -> List[Dict[str, Any]]:
    """
    Load results CSV from a Synergy experiment.

    The CSV has columns: item_id, config_name, status, time_ms, urc_flag

    Args:
        results_csv: Path to results.csv

    Returns:
        List of result dictionaries
    """
    results = []
    with open(results_csv, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            results.append({
                'item_id': row['item_id'],
                'config_name': row['config_name'],
                'status': row['status'],
                'time_ms': float(row['time_ms']),
                'urc_flag': int(row['urc_flag'])
            })
    logger.info(f"Loaded {len(results)} results from {results_csv}")
    return results


def load_error_traces(traces_jsonl: Path) -> Dict[str, Dict[str, Any]]:
    """
    Load error traces JSONL.

    Args:
        traces_jsonl: Path to error_traces.jsonl

    Returns:
        Dictionary mapping (item_id, config_name) -> trace dict
    """
    traces = {}
    if not traces_jsonl.exists():
        logger.warning(f"Error traces file not found: {traces_jsonl}")
        return traces

    with open(traces_jsonl, 'r') as f:
        for line in f:
            trace = json.loads(line.strip())
            key = (trace['item_id'], trace['config_name'])
            traces[key] = trace

    logger.info(f"Loaded {len(traces)} error traces from {traces_jsonl}")
    return traces


def build_joint_results_table(
    results: List[Dict[str, Any]],
    traces: Dict[Tuple[str, str], Dict[str, Any]]
) -> Dict[str, LemmaRecord]:
    """
    Build unified per-lemma table aligning all 4 configurations.

    Args:
        results: List of result dicts from results.csv
        traces: Dict mapping (item_id, config_name) -> trace dict

    Returns:
        Dictionary mapping lemma_id -> LemmaRecord
    """
    # Group by lemma_id
    by_lemma = defaultdict(dict)
    for result in results:
        lemma_id = result['item_id']
        config = result['config_name']
        by_lemma[lemma_id][config] = result

    # Build unified records
    joint_table = {}
    for lemma_id, configs in by_lemma.items():
        record = LemmaRecord(lemma_id=lemma_id)

        # Populate from each configuration
        for config_name, config_result in configs.items():
            status = config_result['status']
            runtime = config_result['time_ms']
            urc = config_result['urc_flag']

            # Get error trace if available
            trace = traces.get((lemma_id, config_name), {})
            error_msg = trace.get('error_message', '')

            # Map to record fields
            if config_name == "Baseline-RAG":
                record.baseline_status = status
                record.baseline_runtime = runtime
                record.baseline_urc = urc
                record.baseline_error = error_msg
            elif config_name == "SAPSE-Strict":
                record.strict_status = status
                record.strict_runtime = runtime
                record.strict_urc = urc
                record.strict_error = error_msg
            elif config_name == "SAPSE-Fast":
                record.fast_status = status
                record.fast_runtime = runtime
                record.fast_urc = urc
                record.fast_error = error_msg
            elif config_name == "SAPSE-Synergy":
                record.synergy_status = status
                record.synergy_runtime = runtime
                record.synergy_urc = urc
                record.synergy_error = error_msg

        joint_table[lemma_id] = record

    logger.info(f"Built joint table with {len(joint_table)} lemmas")
    return joint_table


def save_joint_table(joint_table: Dict[str, LemmaRecord], output_csv: Path):
    """Save joint table to CSV."""
    output_csv.parent.mkdir(parents=True, exist_ok=True)

    with open(output_csv, 'w', newline='') as f:
        if not joint_table:
            logger.warning("Joint table is empty, skipping save")
            return

        fieldnames = list(asdict(next(iter(joint_table.values()))).keys())
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()

        for record in joint_table.values():
            writer.writerow(record.to_dict())

    logger.info(f"Saved joint table to {output_csv}")


# ============================================================================
# Task 1: Fragment Coverage Analysis
# ============================================================================

def in_verified_fragment(coq_stmt: str) -> bool:
    """
    Check if a Coq statement uses only constructs from the verified Rocq fragment.

    This is a heuristic checker that determines whether the lemma operates within
    the mechanically verified minimal calculus subset.

    ALLOWED patterns:
    - forall, ->, basic arrows
    - Propositional equality (=)
    - Basic inductive types (nat, bool, list, etc.)
    - Standard library imports (Coq.Lists.List, Coq.ZArith.ZArith, etc.)

    DISALLOWED patterns:
    - Typeclasses (Class, Instance, Context, `{...}`)
    - Canonical structures
    - Program features (Program, Obligation)
    - Ssreflect syntax (have, by, apply:, etc.)
    - Tactics notation

    Args:
        coq_stmt: Coq lemma statement string

    Returns:
        True if statement is in verified fragment
    """
    # Normalize whitespace
    stmt = " ".join(coq_stmt.split())

    # DISALLOWED patterns
    disallowed_patterns = [
        r'\bClass\b',
        r'\bInstance\b',
        r'\bContext\b',
        r'\{[^}]*\bforall\b',  # Typeclass constraints like {forall ...}
        r'\bCanonical\b',
        r'\bProgram\b',
        r'\bObligation\b',
        r'\bhave\b',  # Ssreflect
        r'\bby\b\s+\[',  # Ssreflect by [...]
        r'apply\s*:',  # Ssreflect apply:
        r'\bmove\s*=\s*>',  # Ssreflect move=>
        r'Notation\s+"',  # Custom notation
        r'\#\[',  # Attributes (modern Coq)
    ]

    for pattern in disallowed_patterns:
        if re.search(pattern, stmt, re.IGNORECASE):
            return False

    # If no disallowed patterns found, assume it's in fragment
    return True


def annotate_fragment_coverage(
    joint_table: Dict[str, LemmaRecord],
    data_jsonl: Path
) -> None:
    """
    Annotate each lemma with fragment coverage (in_frag_* fields).

    Args:
        joint_table: Joint results table to annotate (modified in place)
        data_jsonl: Path to input data JSONL with 'draft' field
    """
    # Load draft statements from input data
    drafts = {}
    if data_jsonl.exists():
        with open(data_jsonl, 'r') as f:
            for line in f:
                item = json.loads(line.strip())
                lemma_id = item.get('id', '')
                draft = item.get('draft', '')
                drafts[lemma_id] = draft

    logger.info(f"Loaded {len(drafts)} draft statements")

    # Annotate each record
    for lemma_id, record in joint_table.items():
        draft = drafts.get(lemma_id, '')

        # For simplicity, check the draft statement for all configs
        # (In reality, we'd want to check final ASTs, but those aren't easily available)
        in_frag = in_verified_fragment(draft)

        record.in_frag_baseline = in_frag
        record.in_frag_strict = in_frag
        record.in_frag_fast = in_frag
        record.in_frag_synergy = in_frag
        record.raw_ast = draft[:500]  # Store first 500 chars

    logger.info("Annotated fragment coverage for all lemmas")


def analyze_fragment_coverage(
    joint_table: Dict[str, LemmaRecord],
    output_dir: Path
) -> None:
    """
    Analyze fragment coverage and generate summary CSV and LaTeX table.

    Args:
        joint_table: Joint results table
        output_dir: Output directory
    """
    logger.info("Analyzing fragment coverage...")

    # Group by category and compute stats
    # First, ensure categories are assigned (will be done in Task 2)
    # For now, use a placeholder "All" category

    stats_list = []

    # Overall stats
    total = len(joint_table)
    in_frag_count = sum(1 for r in joint_table.values() if r.in_frag_synergy)
    in_frag_ratio = in_frag_count / total if total > 0 else 0.0

    synergy_verified_in_frag = sum(
        1 for r in joint_table.values()
        if r.in_frag_synergy and r.synergy_status == "Verified"
    )
    synergy_verified_out_frag = sum(
        1 for r in joint_table.values()
        if not r.in_frag_synergy and r.synergy_status == "Verified"
    )

    stats = FragmentCoverageStats(
        category="All",
        num_lemmas=total,
        in_frag_count=in_frag_count,
        in_frag_ratio=in_frag_ratio,
        synergy_verified_in_frag=synergy_verified_in_frag,
        synergy_verified_out_frag=synergy_verified_out_frag
    )
    stats_list.append(stats)

    # Save CSV
    csv_path = output_dir / "fragment_coverage_summary.csv"
    with open(csv_path, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(stats.to_dict().keys()))
        writer.writeheader()
        for s in stats_list:
            writer.writerow(s.to_dict())

    logger.info(f"Saved fragment coverage summary to {csv_path}")

    # Generate LaTeX table
    latex_dir = output_dir / "latex"
    latex_dir.mkdir(exist_ok=True)
    latex_path = latex_dir / "fragment_coverage.tex"

    with open(latex_path, 'w') as f:
        f.write("\\begin{tabular}{lrrrr}\n")
        f.write("\\toprule\n")
        f.write("Category & \\#Lemmas & InFrag (\\%) & Synergy verified in-frag (\\%) & Synergy verified out-of-frag (\\%) \\\\\n")
        f.write("\\midrule\n")

        for s in stats_list:
            in_frag_pct = s.in_frag_ratio * 100
            verified_in_pct = (s.synergy_verified_in_frag / s.in_frag_count * 100
                             if s.in_frag_count > 0 else 0.0)
            verified_out_pct = (s.synergy_verified_out_frag / (s.num_lemmas - s.in_frag_count) * 100
                               if (s.num_lemmas - s.in_frag_count) > 0 else 0.0)

            f.write(f"{s.category} & {s.num_lemmas} & {in_frag_pct:.1f} & "
                   f"{verified_in_pct:.1f} & {verified_out_pct:.1f} \\\\\n")

        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")

    logger.info(f"Saved LaTeX fragment coverage table to {latex_path}")


# ============================================================================
# Task 2: Semantic Category Breakdown
# ============================================================================

def categorize_lemma(lemma_id: str) -> str:
    """
    Assign semantic category based on lemma ID.

    Categories:
    - Arithmetic: Z, nat, N, Q operations
    - Boolean: bool, and, or, negation
    - List: list, append, map, fold
    - Inductive: custom inductive types, pattern matching
    - Misc: everything else

    Args:
        lemma_id: Lemma identifier (typically CompCert:Module:lemma_name)

    Returns:
        Category name
    """
    # Extract module/file hints from ID
    lower_id = lemma_id.lower()

    # Arithmetic patterns
    if any(kw in lower_id for kw in ['zarith', 'nat', 'integer', 'int', 'add', 'mul', 'sub', 'div']):
        return "Arithmetic"

    # Boolean patterns
    if any(kw in lower_id for kw in ['bool', 'and', 'or', 'neg', 'true', 'false']):
        return "Boolean"

    # List patterns
    if any(kw in lower_id for kw in ['list', 'append', 'map', 'fold', 'cons', 'nil']):
        return "List"

    # Inductive patterns
    if any(kw in lower_id for kw in ['inductive', 'match', 'case', 'tree', 'option']):
        return "Inductive"

    # Default
    return "Misc"


def annotate_categories(joint_table: Dict[str, LemmaRecord]) -> None:
    """
    Annotate each lemma with semantic category.

    Args:
        joint_table: Joint results table (modified in place)
    """
    for lemma_id, record in joint_table.items():
        record.category = categorize_lemma(lemma_id)

    logger.info("Annotated semantic categories for all lemmas")


def analyze_categories(
    joint_table: Dict[str, LemmaRecord],
    output_dir: Path
) -> None:
    """
    Analyze semantic categories and generate summary CSV and LaTeX table.

    Args:
        joint_table: Joint results table
        output_dir: Output directory
    """
    logger.info("Analyzing semantic categories...")

    # Group by category
    by_category = defaultdict(list)
    for record in joint_table.values():
        by_category[record.category].append(record)

    stats_list = []

    for category, records in sorted(by_category.items()):
        num_lemmas = len(records)

        verified_baseline = sum(1 for r in records if r.baseline_status == "Verified")
        verified_strict = sum(1 for r in records if r.strict_status == "Verified")
        verified_fast = sum(1 for r in records if r.fast_status == "Verified")
        verified_synergy = sum(1 for r in records if r.synergy_status == "Verified")

        abstained_strict = sum(1 for r in records if r.strict_status == "Abstained")
        abstained_synergy = sum(1 for r in records if r.synergy_status == "Abstained")

        stats = CategoryStats(
            category=category,
            num_lemmas=num_lemmas,
            verified_baseline=verified_baseline,
            verified_strict=verified_strict,
            verified_fast=verified_fast,
            verified_synergy=verified_synergy,
            abstained_strict=abstained_strict,
            abstained_synergy=abstained_synergy
        )
        stats_list.append(stats)

    # Save CSV
    csv_path = output_dir / "category_results.csv"
    with open(csv_path, 'w', newline='') as f:
        fieldnames = list(stats_list[0].to_dict().keys())
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for s in stats_list:
            writer.writerow(s.to_dict())

    logger.info(f"Saved category results to {csv_path}")

    # Generate LaTeX table
    latex_dir = output_dir / "latex"
    latex_dir.mkdir(exist_ok=True)
    latex_path = latex_dir / "category_results.tex"

    with open(latex_path, 'w') as f:
        f.write("\\begin{tabular}{lcccc}\n")
        f.write("\\toprule\n")
        f.write("Category & Baseline-RAG & Strict & Fast & Synergy \\\\\n")
        f.write("\\midrule\n")

        for s in stats_list:
            baseline_pct = s.verified_baseline / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0
            strict_pct = s.verified_strict / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0
            fast_pct = s.verified_fast / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0
            synergy_pct = s.verified_synergy / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0

            f.write(f"{s.category} & {baseline_pct:.1f}\\% & {strict_pct:.1f}\\% & "
                   f"{fast_pct:.1f}\\% & {synergy_pct:.1f}\\% \\\\\n")

        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")

    logger.info(f"Saved LaTeX category table to {latex_path}")


# ============================================================================
# Task 3: Structural Complexity Analysis
# ============================================================================

def compute_ast_metrics(coq_stmt: str) -> Tuple[int, int]:
    """
    Compute approximate AST depth and binder count from Coq statement.

    Args:
        coq_stmt: Coq statement string

    Returns:
        (ast_depth, binder_count)
    """
    # Simple heuristics:
    # - AST depth: max nesting level of parentheses/braces
    # - Binder count: number of 'forall' keywords

    depth = 0
    max_depth = 0

    for char in coq_stmt:
        if char in '({[':
            depth += 1
            max_depth = max(max_depth, depth)
        elif char in ')}]':
            depth = max(0, depth - 1)

    binder_count = len(re.findall(r'\bforall\b', coq_stmt))

    return max_depth, binder_count


def assign_complexity_band(depth: int, binder_count: int) -> str:
    """
    Assign complexity band based on AST metrics.

    Args:
        depth: AST depth
        binder_count: Number of binders

    Returns:
        "shallow", "medium", or "deep"
    """
    # Heuristic: combine depth and binder count
    complexity_score = depth + binder_count * 2

    if complexity_score <= 8:
        return "shallow"
    elif complexity_score <= 16:
        return "medium"
    else:
        return "deep"


def annotate_complexity(joint_table: Dict[str, LemmaRecord]) -> None:
    """
    Annotate each lemma with complexity metrics.

    Args:
        joint_table: Joint results table (modified in place)
    """
    for record in joint_table.values():
        depth, binder_count = compute_ast_metrics(record.raw_ast)
        record.ast_depth = depth
        record.binder_count = binder_count
        record.complexity_band = assign_complexity_band(depth, binder_count)

    logger.info("Annotated complexity metrics for all lemmas")


def analyze_complexity(
    joint_table: Dict[str, LemmaRecord],
    output_dir: Path
) -> None:
    """
    Analyze structural complexity and generate summary CSV and LaTeX table.

    Args:
        joint_table: Joint results table
        output_dir: Output directory
    """
    logger.info("Analyzing structural complexity...")

    # Group by complexity band
    by_band = defaultdict(list)
    for record in joint_table.values():
        by_band[record.complexity_band].append(record)

    stats_list = []

    for band in ["shallow", "medium", "deep"]:
        records = by_band[band]
        num_lemmas = len(records)

        if num_lemmas == 0:
            continue

        verified_baseline = sum(1 for r in records if r.baseline_status == "Verified")
        verified_strict = sum(1 for r in records if r.strict_status == "Verified")
        verified_fast = sum(1 for r in records if r.fast_status == "Verified")
        verified_synergy = sum(1 for r in records if r.synergy_status == "Verified")

        abstained_strict = sum(1 for r in records if r.strict_status == "Abstained")
        abstained_synergy = sum(1 for r in records if r.synergy_status == "Abstained")

        stats = ComplexityStats(
            band=band,
            num_lemmas=num_lemmas,
            verified_baseline=verified_baseline,
            verified_strict=verified_strict,
            verified_fast=verified_fast,
            verified_synergy=verified_synergy,
            abstained_strict=abstained_strict,
            abstained_synergy=abstained_synergy
        )
        stats_list.append(stats)

    # Save CSV
    csv_path = output_dir / "complexity_results.csv"
    with open(csv_path, 'w', newline='') as f:
        if stats_list:
            fieldnames = list(stats_list[0].to_dict().keys())
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            for s in stats_list:
                writer.writerow(s.to_dict())

    logger.info(f"Saved complexity results to {csv_path}")

    # Generate LaTeX table
    latex_dir = output_dir / "latex"
    latex_dir.mkdir(exist_ok=True)
    latex_path = latex_dir / "complexity_results.tex"

    with open(latex_path, 'w') as f:
        f.write("\\begin{tabular}{lcccc}\n")
        f.write("\\toprule\n")
        f.write("Complexity band & Baseline-RAG & Strict & Fast & Synergy \\\\\n")
        f.write("\\midrule\n")

        for s in stats_list:
            baseline_pct = s.verified_baseline / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0
            strict_pct = s.verified_strict / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0
            fast_pct = s.verified_fast / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0
            synergy_pct = s.verified_synergy / s.num_lemmas * 100 if s.num_lemmas > 0 else 0.0

            f.write(f"{s.band} & {baseline_pct:.1f}\\% & {strict_pct:.1f}\\% & "
                   f"{fast_pct:.1f}\\% & {synergy_pct:.1f}\\% \\\\\n")

        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")

    logger.info(f"Saved LaTeX complexity table to {latex_path}")


# ============================================================================
# Main Analysis Entry Point
# ============================================================================

def main():
    """Main entry point for analysis."""
    parser = argparse.ArgumentParser(
        description="Analyze SAPSE-Synergy 2K experiments",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Build joint table only
  python scripts/analyze_synergy_experiments.py --experiment outputs/synergy_deepseek_real_2k_seed11

  # Run all analyses
  python scripts/analyze_synergy_experiments.py --experiment outputs/synergy_deepseek_real_2k_seed11 --all

  # Run specific analyses
  python scripts/analyze_synergy_experiments.py --experiment outputs/synergy_deepseek_real_2k_seed11 \\
      --fragment --category --complexity --lost-successes
        """
    )

    parser.add_argument(
        "--experiment",
        type=str,
        required=True,
        help="Path to experiment directory (e.g., outputs/synergy_deepseek_real_2k_seed11)"
    )

    parser.add_argument(
        "--output-dir",
        type=str,
        default="outputs/analysis",
        help="Output directory for analysis results (default: outputs/analysis)"
    )

    # Analysis flags
    parser.add_argument("--all", action="store_true", help="Run all analyses")
    parser.add_argument("--fragment", action="store_true", help="Fragment coverage analysis")
    parser.add_argument("--category", action="store_true", help="Semantic category breakdown")
    parser.add_argument("--complexity", action="store_true", help="Structural complexity analysis")
    parser.add_argument("--core-vs-fast", action="store_true", help="Verified core vs Fast comparison")
    parser.add_argument("--baselines", action="store_true", help="Extra baselines comparison")
    parser.add_argument("--lost-successes", action="store_true", help="Lost successes differential analysis")

    args = parser.parse_args()

    # Setup paths
    experiment_dir = Path(args.experiment)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    results_csv = experiment_dir / "results.csv"
    traces_jsonl = experiment_dir / "error_traces.jsonl"

    if not results_csv.exists():
        logger.error(f"Results file not found: {results_csv}")
        return

    # Load data
    logger.info("Loading experiment results...")
    results = load_synergy_results(results_csv)
    traces = load_error_traces(traces_jsonl)

    # Build joint table
    logger.info("Building joint per-lemma results table...")
    joint_table = build_joint_results_table(results, traces)

    # Save joint table
    joint_table_csv = output_dir / "joint_results_2k.csv"
    save_joint_table(joint_table, joint_table_csv)

    logger.info(f"Joint table saved to {joint_table_csv}")
    logger.info(f"Total lemmas: {len(joint_table)}")

    # Determine data_jsonl path (input data with drafts)
    data_jsonl = Path("data/synergy_rag_2k.jsonl")  # Default
    # Try to auto-detect from experiment config if available
    config_yaml = experiment_dir / "config.yaml"
    if config_yaml.exists():
        import yaml
        with open(config_yaml, 'r') as f:
            exp_config = yaml.safe_load(f)
            data_path = exp_config.get('data', {}).get('nl_steps_path')
            if data_path:
                data_jsonl = Path(data_path)

    # PART I: Extended Experiment Analysis
    logger.info("=" * 60)
    logger.info("PART I: Extended Experiment Analysis")
    logger.info("=" * 60)

    # Pre-processing: annotate all metadata
    logger.info("Annotating metadata (categories, complexity, fragment coverage)...")
    annotate_categories(joint_table)
    annotate_complexity(joint_table)
    annotate_fragment_coverage(joint_table, data_jsonl)

    # Re-save joint table with annotations
    save_joint_table(joint_table, joint_table_csv)
    logger.info(f"Updated joint table with annotations: {joint_table_csv}")

    # Task 1: Fragment coverage
    if args.all or args.fragment:
        analyze_fragment_coverage(joint_table, output_dir)

    # Task 2: Category breakdown
    if args.all or args.category:
        analyze_categories(joint_table, output_dir)

    # Task 3: Complexity analysis
    if args.all or args.complexity:
        analyze_complexity(joint_table, output_dir)

    # Task 4: Core vs Fast (placeholder for now)
    if args.all or args.core_vs_fast:
        logger.warning("Core vs Fast analysis not yet implemented (requires instrumentation)")

    # Task 5: Extra baselines (placeholder for now)
    if args.all or args.baselines:
        logger.warning("Extra baselines analysis not yet implemented (requires new experiments)")

    # PART II: Lost-Success Differential Analysis
    if args.all or args.lost_successes:
        try:
            import sys
            sys.path.insert(0, str(Path(__file__).parent))
            from utils.lost_success_analysis import run_lost_success_analysis
            run_lost_success_analysis(joint_table, output_dir)
        except ImportError as e:
            logger.error(f"Failed to import lost_success_analysis module: {e}")

    logger.info("=" * 60)
    logger.info("Analysis complete!")
    logger.info("=" * 60)
    logger.info(f"Output directory: {output_dir}")
    logger.info(f"Joint table: {joint_table_csv}")
    logger.info("Check outputs/analysis/ for CSV files and outputs/analysis/latex/ for LaTeX tables")


if __name__ == "__main__":
    main()
