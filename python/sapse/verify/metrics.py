"""Evaluation metrics for SAPSE pipeline."""

import re
from typing import Dict, List

import numpy as np
from loguru import logger


class PipelineMetrics:
    """
    Compute and track evaluation metrics for SAPSE.

    Tracks: conversion rate, lemma yield, recall, MAP, proof success.

    Example:
        >>> metrics = PipelineMetrics()
        >>> metrics.add_verification_result("passed")
        >>> metrics.add_retrieval_metrics(0.85, 0.72)
        >>> summary = metrics.compute_summary()
        >>> print(summary["conversion_rate"])
    """

    def __init__(self):
        """Initialize metrics tracker."""
        self.verification_results: List[str] = []
        self.retrieval_recalls: List[float] = []
        self.retrieval_maps: List[float] = []
        self.proof_successes: List[bool] = []

        logger.debug("Initialized PipelineMetrics")

    def add_verification_result(self, status: str):
        """
        Add a verification result.

        Args:
            status: Verification status ('passed', 'failed', 'fixable', 'error').

        Example:
            >>> metrics.add_verification_result("passed")
        """
        self.verification_results.append(status)

    def add_retrieval_metrics(self, recall: float, map_score: float):
        """
        Add retrieval evaluation metrics.

        Args:
            recall: Recall@k score.
            map_score: MAP@k score.

        Example:
            >>> metrics.add_retrieval_metrics(0.8, 0.75)
        """
        self.retrieval_recalls.append(recall)
        self.retrieval_maps.append(map_score)

    def add_proof_success(self, success: bool):
        """
        Add proof success indicator.

        Args:
            success: Whether proof was successfully automated.

        Example:
            >>> metrics.add_proof_success(True)
        """
        self.proof_successes.append(success)

    def compute_summary(self) -> Dict[str, float]:
        """
        Compute summary of all metrics.

        Returns:
            Dictionary with metric names and values.

        Example:
            >>> summary = metrics.compute_summary()
            >>> print(f"Conversion rate: {summary['conversion_rate']:.2%}")
        """
        summary = {}

        # Conversion rate: ratio of verified lemmas
        if self.verification_results:
            passed = sum(
                1 for r in self.verification_results if r == "passed"
            )
            summary["conversion_rate"] = passed / len(self.verification_results)
            summary["lemma_yield"] = passed
            summary["total_attempts"] = len(self.verification_results)

            # Breakdown by status
            summary["passed_count"] = passed
            summary["failed_count"] = sum(
                1 for r in self.verification_results if r == "failed"
            )
            summary["fixable_count"] = sum(
                1 for r in self.verification_results if r == "fixable"
            )
            summary["error_count"] = sum(
                1 for r in self.verification_results if r == "error"
            )
        else:
            summary["conversion_rate"] = 0.0
            summary["lemma_yield"] = 0
            summary["total_attempts"] = 0

        # Retrieval metrics
        if self.retrieval_recalls:
            summary["recall_at_k"] = np.mean(self.retrieval_recalls)
            summary["recall_std"] = np.std(self.retrieval_recalls)

        if self.retrieval_maps:
            summary["map_at_k"] = np.mean(self.retrieval_maps)
            summary["map_std"] = np.std(self.retrieval_maps)

        # Proof success rate
        if self.proof_successes:
            summary["proof_success_rate"] = sum(self.proof_successes) / len(
                self.proof_successes
            )

        return summary

    def print_summary(self):
        """
        Print formatted metrics summary.

        Example:
            >>> metrics.print_summary()
        """
        summary = self.compute_summary()

        print("\n" + "=" * 60)
        print("SAPSE Pipeline Metrics Summary")
        print("=" * 60)

        if "conversion_rate" in summary:
            print(f"\nVerification:")
            print(f"  Conversion Rate:  {summary['conversion_rate']:.2%}")
            print(f"  Lemma Yield:      {summary['lemma_yield']}")
            print(f"  Total Attempts:   {summary['total_attempts']}")

            if "passed_count" in summary:
                print(f"\n  Breakdown:")
                print(f"    Passed:   {summary['passed_count']}")
                print(f"    Failed:   {summary['failed_count']}")
                print(f"    Fixable:  {summary['fixable_count']}")
                print(f"    Error:    {summary['error_count']}")

        if "recall_at_k" in summary:
            print(f"\nRetrieval:")
            print(
                f"  Recall@k:  {summary['recall_at_k']:.3f} ± {summary.get('recall_std', 0):.3f}"
            )

        if "map_at_k" in summary:
            print(
                f"  MAP@k:     {summary['map_at_k']:.3f} ± {summary.get('map_std', 0):.3f}"
            )

        if "proof_success_rate" in summary:
            print(f"\nProof Automation:")
            print(f"  Success Rate:  {summary['proof_success_rate']:.2%}")

        print("=" * 60 + "\n")

    def save_to_dict(self) -> Dict:
        """
        Export all raw data and summary.

        Returns:
            Dictionary with raw data and computed metrics.

        Example:
            >>> data = metrics.save_to_dict()
            >>> import json
            >>> json.dump(data, open("metrics.json", "w"))
        """
        return {
            "raw_data": {
                "verification_results": self.verification_results,
                "retrieval_recalls": self.retrieval_recalls,
                "retrieval_maps": self.retrieval_maps,
                "proof_successes": self.proof_successes,
            },
            "summary": self.compute_summary(),
        }


def aggregate_error_taxonomy(results: List[Dict]) -> Dict:
    """
    Aggregate error taxonomy from verification results.

    Categorizes errors into:
    - MissingType: Type annotation errors
    - MissingRequire: Missing Require Import statements
    - Syntax: Syntax errors
    - Timeout: Verification timeouts
    - SemanticGap: Semantic or proof gaps

    Args:
        results: List of verification result dictionaries

    Returns:
        Dictionary with error taxonomy breakdown

    Example:
        >>> results = [
        ...     {"verify_status": "failed", "verify_message": "The reference nat was not found"},
        ...     {"verify_status": "fixable", "verify_message": "Syntax error: expecting '.'"}
        ... ]
        >>> taxonomy = aggregate_error_taxonomy(results)
        >>> print(taxonomy["MissingType"]["total"])
        1
    """
    taxonomy = {
        "MissingType": {"total": 0, "fixable": 0, "passed_after_fix": 0},
        "MissingRequire": {"total": 0, "fixable": 0, "passed_after_fix": 0},
        "Syntax": {"total": 0, "fixable": 0, "passed_after_fix": 0},
        "Timeout": {"total": 0, "fixable": 0, "passed_after_fix": 0},
        "SemanticGap": {"total": 0, "fixable": 0, "passed_after_fix": 0},
        "Other": {"total": 0, "fixable": 0, "passed_after_fix": 0},
    }

    # Error pattern matchers
    type_patterns = [
        r"type.*not found",
        r"cannot infer.*type",
        r"has type.*but is expected",
        r"unbound.*variable",
    ]
    require_patterns = [
        r"reference.*not found",
        r"unknown.*module",
        r"no such.*library",
    ]
    syntax_patterns = [
        r"syntax error",
        r"expecting",
        r"unexpected",
        r"parse error",
    ]
    timeout_patterns = [
        r"timeout",
        r"timed out",
    ]

    for result in results:
        status = result.get("verify_status", "error")
        message = result.get("verify_message", "").lower()
        fixed = result.get("fixed_by_sanitizer", False)

        # Skip passed results
        if status == "passed":
            continue

        # Determine error category
        error_type = "Other"
        for pattern in type_patterns:
            if re.search(pattern, message, re.IGNORECASE):
                error_type = "MissingType"
                break
        if error_type == "Other":
            for pattern in require_patterns:
                if re.search(pattern, message, re.IGNORECASE):
                    error_type = "MissingRequire"
                    break
        if error_type == "Other":
            for pattern in syntax_patterns:
                if re.search(pattern, message, re.IGNORECASE):
                    error_type = "Syntax"
                    break
        if error_type == "Other":
            for pattern in timeout_patterns:
                if re.search(pattern, message, re.IGNORECASE):
                    error_type = "Timeout"
                    break
        if error_type == "Other" and status == "failed":
            error_type = "SemanticGap"

        # Update counts
        taxonomy[error_type]["total"] += 1
        if status == "fixable":
            taxonomy[error_type]["fixable"] += 1
        if fixed and result.get("verify_status_after_fix") == "passed":
            taxonomy[error_type]["passed_after_fix"] += 1

    # Compute conversion rates
    for error_type, counts in taxonomy.items():
        if counts["fixable"] > 0:
            counts["conversion_rate"] = counts["passed_after_fix"] / counts["fixable"]
        else:
            counts["conversion_rate"] = 0.0

    return taxonomy


def compare_hammer_gain(coq_only_results: List[Dict], hammer_results: List[Dict]) -> Dict:
    """
    Compare Coq-only vs CoqHammer+Coq results to measure hammer effectiveness.

    Args:
        coq_only_results: Results from Coq-only verification
        hammer_results: Results from Coq+Hammer verification

    Returns:
        Dictionary with delta metrics

    Example:
        >>> coq_results = [{"verify_status": "passed"}, {"verify_status": "failed"}]
        >>> hammer_results = [{"verify_status": "passed"}, {"verify_status": "passed"}]
        >>> delta = compare_hammer_gain(coq_results, hammer_results)
        >>> print(delta["delta_passed"])
        1
    """
    coq_passed = sum(1 for r in coq_only_results if r.get("verify_status") == "passed")
    hammer_passed = sum(1 for r in hammer_results if r.get("verify_status") == "passed")

    coq_total = len(coq_only_results)
    hammer_total = len(hammer_results)

    coq_rate = coq_passed / coq_total if coq_total > 0 else 0.0
    hammer_rate = hammer_passed / hammer_total if hammer_total > 0 else 0.0

    # Extract wall times if available
    coq_time = sum(r.get("wall_time_sec", 0) for r in coq_only_results)
    hammer_time = sum(r.get("wall_time_sec", 0) for r in hammer_results)

    return {
        "coq_only_passed": coq_passed,
        "hammer_passed": hammer_passed,
        "delta_passed": hammer_passed - coq_passed,
        "coq_only_rate": coq_rate,
        "hammer_rate": hammer_rate,
        "delta_pass_rate": hammer_rate - coq_rate,
        "coq_wall_time_sec": coq_time,
        "hammer_wall_time_sec": hammer_time,
        "delta_wall_time_sec": hammer_time - coq_time,
    }
