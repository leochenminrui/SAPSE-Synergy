#!/usr/bin/env python3
"""Main experiment runner for Synergy evaluation.

Runs all four pipelines (Baseline-RAG, SAPSE-Strict, SAPSE-Fast, SAPSE-Synergy)
on the full dataset and generates results CSV + aggregated table.

Usage:
    python scripts/run_synergy_experiments.py --input data/nl_proofs.jsonl --limit 100
    python scripts/run_synergy_experiments.py --config configs/synergy.yaml
"""

import argparse
import csv
import json
from pathlib import Path
from typing import List, Dict, Any
from collections import defaultdict
from loguru import logger

from sapse.sanitize.pipelines import create_pipeline
from sapse.verify import create_verifier
from sapse.datasets import DatasetLoader
from sapse.config import Config


def load_input_data(input_file: str, limit: int = None) -> List[Dict[str, Any]]:
    """Load input data from JSONL file.

    Args:
        input_file: Path to input JSONL file
        limit: Optional limit on number of items to process

    Returns:
        List of items with 'id' and 'text' fields
    """
    loader = DatasetLoader(input_file)
    items = loader.load_all()

    if limit:
        items = items[:limit]

    logger.info(f"Loaded {len(items)} items from {input_file}")
    return items


def get_raw_ast_from_item(item: Dict[str, Any]) -> str:
    """Extract raw AST/Coq code from item.

    Assumes item has either:
    - 'draft' field (from abstractor output)
    - 'text' field (generic text)
    - 'coq_code' field (explicit Coq code)

    Args:
        item: Input item dict

    Returns:
        Raw Coq code string
    """
    if 'draft' in item:
        return item['draft']
    elif 'coq_code' in item:
        return item['coq_code']
    elif 'text' in item:
        return item['text']
    else:
        raise ValueError(f"Item missing 'draft', 'coq_code', or 'text' field: {item}")


def create_verifier_fn(config: Config):
    """Create verifier function from config.

    Args:
        config: Configuration object

    Returns:
        Verifier function
    """
    use_mock = config.get("verify.use_mock", False)
    coqc_path = config.get("verify.coqc_path", "coqc")
    timeout = config.get("verify.timeout", 30)
    random_seed = config.get("verify.random_seed", 0)

    verifier = create_verifier(use_mock=use_mock, coqc_path=coqc_path, timeout=timeout, random_seed=random_seed)

    def verifier_fn(coq_code: str) -> Dict[str, str]:
        """Wrapper to match expected interface."""
        result = verifier.verify(coq_code)
        return result

    return verifier_fn


def run_all_pipelines(
    items: List[Dict[str, Any]],
    verifier_fn,
    output_dir: Path
) -> List[Dict[str, Any]]:
    """Run all four pipelines on all items.

    Args:
        items: List of input items
        verifier_fn: Verifier function
        output_dir: Output directory for results

    Returns:
        List of all results (flattened across pipelines)
    """
    pipeline_names = ["Baseline-RAG", "SAPSE-Strict", "SAPSE-Fast", "SAPSE-Synergy"]
    all_results = []

    for pipeline_name in pipeline_names:
        logger.info(f"Running pipeline: {pipeline_name}")
        pipeline = create_pipeline(pipeline_name, verifier_fn)

        for item in items:
            item_id = item.get('id', f"item_{items.index(item)}")
            raw_ast = get_raw_ast_from_item(item)

            try:
                result = pipeline.process_item(item_id, raw_ast)
                all_results.append(result)

                # Log progress every 100 items
                if len(all_results) % 100 == 0:
                    logger.info(f"Processed {len(all_results)} items across pipelines")

            except Exception as e:
                logger.error(f"Error processing {item_id} with {pipeline_name}: {e}")
                # Create error result
                from sapse.sanitize.pipelines import PipelineResult
                error_result = PipelineResult(
                    item_id=item_id,
                    config_name=pipeline_name,
                    status="Error",
                    time_ms=0.0,
                    urc_flag=0,
                    raw_ast=raw_ast,
                    final_ast=raw_ast,
                    error_message=str(e)
                )
                all_results.append(error_result)

    logger.info(f"Total results: {len(all_results)}")
    return all_results


def save_results_csv(results: List, output_file: Path):
    """Save results to CSV file.

    Args:
        results: List of PipelineResult objects
        output_file: Path to output CSV file
    """
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['item_id', 'config_name', 'status', 'time_ms', 'urc_flag'])

        for result in results:
            writer.writerow([
                result.item_id,
                result.config_name,
                result.status,
                f"{result.time_ms:.2f}",
                result.urc_flag
            ])

    logger.info(f"Results saved to {output_file}")


def save_error_traces(results: List, output_file: Path):
    """Save detailed error traces to JSONL for analysis.

    Args:
        results: List of PipelineResult objects
        output_file: Path to output JSONL file
    """
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w') as f:
        for result in results:
            trace = {
                'item_id': result.item_id,
                'config_name': result.config_name,
                'status': result.status,
                'time_ms': result.time_ms,
                'urc_flag': result.urc_flag,
                'error_message': result.error_message,
                'abstain_reason': getattr(result, 'abstain_reason', None),
                'last_pass_applied': getattr(result, 'last_pass_applied', None),
                'guard_failures': getattr(result, 'guard_failures', None),
                'admissibility_failures': result.admissibility_failures
            }
            f.write(json.dumps(trace) + '\n')

    logger.info(f"Error traces saved to {output_file}")


def generate_aggregated_table(results: List, output_file: Path):
    """Generate aggregated markdown table.

    Args:
        results: List of PipelineResult objects
        output_file: Path to output markdown file
    """
    # Group by config_name
    by_config = defaultdict(list)
    for result in results:
        by_config[result.config_name].append(result)

    # Compute statistics
    rows = []
    pipeline_order = ["Baseline-RAG", "SAPSE-Strict", "SAPSE-Fast", "SAPSE-Synergy"]

    for config_name in pipeline_order:
        results_for_config = by_config[config_name]
        total = len(results_for_config)

        if total == 0:
            continue

        verified = sum(1 for r in results_for_config if r.status == "Verified")
        abstained = sum(1 for r in results_for_config if r.status == "Abstained")
        failed = sum(1 for r in results_for_config if r.status == "Failed")
        urc_sum = sum(r.urc_flag for r in results_for_config)

        verified_pct = (verified / total) * 100 if total > 0 else 0.0
        abstained_pct = (abstained / total) * 100 if total > 0 else 0.0

        avg_time = sum(r.time_ms for r in results_for_config) / total if total > 0 else 0.0
        avg_time_s = avg_time / 1000.0

        # Determine Guards column
        if config_name == "Baseline-RAG":
            guards = "None"
        elif config_name == "SAPSE-Strict":
            guards = "VC-Guarded"
        elif config_name == "SAPSE-Fast":
            guards = "None"
        elif config_name == "SAPSE-Synergy":
            guards = "UP-Unguarded → VC-Guarded"
        else:
            guards = "Unknown"

        rows.append({
            'config': config_name,
            'guards': guards,
            'verified_pct': verified_pct,
            'abstained_pct': abstained_pct,
            'avg_time_s': avg_time_s,
            'urc_sum': urc_sum,
            'total': total,
            'verified': verified,
            'abstained': abstained,
            'failed': failed
        })

    # Write markdown table
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w') as f:
        f.write("# Synergy Experiment Results\n\n")
        f.write("## Aggregated Results Table\n\n")
        f.write("| Configuration | Guards | Verified (%) | Abstained (%) | Avg Time (s) | URC (Sum) |\n")
        f.write("|---------------|--------|--------------|---------------|--------------|----------|\n")

        for row in rows:
            f.write(f"| {row['config']} | {row['guards']} | "
                   f"{row['verified_pct']:.1f}% ({row['verified']}/{row['total']}) | "
                   f"{row['abstained_pct']:.1f}% ({row['abstained']}/{row['total']}) | "
                   f"{row['avg_time_s']:.3f} | {row['urc_sum']} |\n")

        f.write("\n## Detailed Statistics\n\n")
        for row in rows:
            f.write(f"### {row['config']}\n\n")
            f.write(f"- **Total items**: {row['total']}\n")
            f.write(f"- **Verified**: {row['verified']} ({row['verified_pct']:.1f}%)\n")
            f.write(f"- **Abstained**: {row['abstained']} ({row['abstained_pct']:.1f}%)\n")
            f.write(f"- **Failed**: {row['failed']}\n")
            f.write(f"- **Average time**: {row['avg_time_s']:.3f}s\n")
            f.write(f"- **URC count**: {row['urc_sum']}\n")
            f.write("\n")

    logger.info(f"Aggregated table saved to {output_file}")


def find_smoking_gun_examples(results: List, output_file: Path, num_examples: int = 2):
    """Find and save smoking gun examples.

    Find cases where:
    - SAPSE-Fast had urc_flag = 1 (Verified with URC)
    - SAPSE-Synergy correctly abstained or failed (no URC)

    Args:
        results: List of PipelineResult objects
        output_file: Path to output file
        num_examples: Number of examples to extract
    """
    # Group by item_id
    by_item = defaultdict(dict)
    for result in results:
        by_item[result.item_id][result.config_name] = result

    smoking_guns = []

    for item_id, item_results in by_item.items():
        fast_result = item_results.get("SAPSE-Fast")
        synergy_result = item_results.get("SAPSE-Synergy")

        if fast_result and synergy_result:
            # Check if Fast had URC and Synergy abstained or had no URC
            if (fast_result.status == "Verified" and fast_result.urc_flag == 1 and
                (synergy_result.status == "Abstained" or synergy_result.urc_flag == 0)):

                smoking_guns.append({
                    'item_id': item_id,
                    'fast_result': fast_result,
                    'synergy_result': synergy_result
                })

    # Take top N
    examples = smoking_guns[:num_examples]

    # Write to file
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w') as f:
        f.write("# Smoking Gun Examples\n\n")
        f.write("Cases where SAPSE-Fast had URC=1 but SAPSE-Synergy correctly abstained:\n\n")

        for i, example in enumerate(examples, 1):
            f.write(f"## Example {i}: {example['item_id']}\n\n")

            f.write(f"### SAPSE-Fast Result\n")
            f.write(f"- **Status**: {example['fast_result'].status}\n")
            f.write(f"- **URC Flag**: {example['fast_result'].urc_flag}\n")
            f.write(f"- **Raw AST**:\n```coq\n{example['fast_result'].raw_ast}\n```\n\n")
            f.write(f"- **Final AST**:\n```coq\n{example['fast_result'].final_ast}\n```\n\n")

            f.write(f"### SAPSE-Synergy Result\n")
            f.write(f"- **Status**: {example['synergy_result'].status}\n")
            f.write(f"- **URC Flag**: {example['synergy_result'].urc_flag}\n")
            if example['synergy_result'].admissibility_failures:
                f.write(f"- **Admissibility Failures**: {example['synergy_result'].admissibility_failures}\n")
            f.write("\n")
            f.write("---\n\n")

    logger.info(f"Smoking gun examples saved to {output_file}")


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="Run synergy experiments")
    parser.add_argument("--input", type=str, required=True,
                       help="Input JSONL file with items")
    parser.add_argument("--output-dir", type=str, default="outputs/synergy",
                       help="Output directory")
    parser.add_argument("--limit", type=int, default=None,
                       help="Limit number of items to process")
    parser.add_argument("--config", type=str, default=None,
                       help="Optional config YAML file")
    parser.add_argument("--use-mock-verifier", action="store_true",
                       help="Use mock verifier (for testing)")
    parser.add_argument("--coq-random-seed", type=int, default=0,
                       help="Random seed passed to Coq verifier for reproducible proof search (default: 0)")
    parser.add_argument("--coq-timeout", type=int, default=30,
                       help="Coq verification timeout in seconds (default: 30)")
    parser.add_argument("--coqc-path", type=str, default="coqc",
                       help="Path to coqc binary (default: coqc)")

    args = parser.parse_args()

    # Load config if provided
    if args.config:
        config = Config.from_yaml(args.config)
    else:
        config = Config({})

    # Override with CLI args
    if args.use_mock_verifier:
        config.set("verify.use_mock", True)

    config.set("verify.random_seed", args.coq_random_seed)
    config.set("verify.timeout", args.coq_timeout)
    config.set("verify.coqc_path", args.coqc_path)

    # Setup output directory
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Load input data
    items = load_input_data(args.input, limit=args.limit)

    if not items:
        logger.error("No items loaded. Exiting.")
        return

    # Create verifier
    verifier_fn = create_verifier_fn(config)

    # Run all pipelines
    logger.info("Starting pipeline execution...")
    results = run_all_pipelines(items, verifier_fn, output_dir)

    # Save results CSV
    csv_file = output_dir / "results.csv"
    save_results_csv(results, csv_file)

    # Save error traces for analysis
    traces_file = output_dir / "error_traces.jsonl"
    save_error_traces(results, traces_file)

    # Generate aggregated table
    table_file = output_dir / "aggregated_table.md"
    generate_aggregated_table(results, table_file)

    # Find smoking gun examples
    examples_file = output_dir / "smoking_gun_examples.md"
    find_smoking_gun_examples(results, examples_file, num_examples=2)

    logger.info("Synergy experiments complete!")
    logger.info(f"Results saved to {output_dir}")
    logger.info(f"- CSV: {csv_file}")
    logger.info(f"- Traces: {traces_file}")
    logger.info(f"- Table: {table_file}")
    logger.info(f"- Examples: {examples_file}")


if __name__ == "__main__":
    main()
