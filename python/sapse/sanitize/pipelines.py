"""Four experimental pipelines for synergy evaluation.

Implements:
1. Baseline-RAG: No sanitization
2. SAPSE-Strict: VC-only (safety-only)
3. SAPSE-Fast: UP-only (coverage-only, may have URC)
4. SAPSE-Synergy: UP + VC (coverage + safety)
"""

import time
from dataclasses import dataclass
from typing import Dict, Any, Optional
from loguru import logger

from .passes import (
    run_pass_1_require,
    run_pass_2_binder_identity,
    run_pass_3_eq_canonical,
    run_pass_4_scope,
    run_pass_5_list,
    run_pass_6_reformat,
    check_admissible_spec,
    find_suspicious_edit,
    apply_utility_passes,
    apply_verified_core_passes,
)


@dataclass
class PipelineResult:
    """Result of pipeline execution."""
    item_id: str
    config_name: str
    status: str  # "Verified", "Failed", "Abstained"
    time_ms: float
    urc_flag: int  # 1 if URC detected, 0 otherwise
    raw_ast: str
    final_ast: str
    admissibility_failures: Optional[list] = None
    error_message: Optional[str] = None
    # Enhanced error tracking fields
    abstain_reason: Optional[str] = None  # Why abstained (guard name)
    last_pass_applied: Optional[str] = None  # Last sanitization pass
    guard_failures: Optional[Dict[str, Any]] = None  # Detailed guard failures


class BasePipeline:
    """Base class for all pipelines."""

    def __init__(self, verifier_fn):
        """Initialize pipeline with verifier function.

        Args:
            verifier_fn: Function that takes Coq code and returns
                        {"status": "Verified"|"Failed", "message": str}
        """
        self.verifier_fn = verifier_fn

    def process_item(self, item_id: str, raw_ast: str) -> PipelineResult:
        """Process a single item through the pipeline.

        Args:
            item_id: Unique identifier for the item
            raw_ast: Raw AST from RAG abstractor

        Returns:
            PipelineResult with status and metrics
        """
        raise NotImplementedError("Subclasses must implement process_item")


class BaselineRAGPipeline(BasePipeline):
    """Pipeline 1: Baseline-RAG.

    No sanitization, direct verification of RAG output.
    """

    def process_item(self, item_id: str, raw_ast: str) -> PipelineResult:
        """Process item: raw_ast -> verify -> log.

        Args:
            item_id: Item identifier
            raw_ast: Raw AST from RAG

        Returns:
            PipelineResult
        """
        start_time = time.time()

        # No transformation, directly verify
        verify_result = self.verifier_fn(raw_ast)
        status = "Verified" if verify_result["status"] == "passed" else "Failed"

        elapsed_ms = (time.time() - start_time) * 1000

        return PipelineResult(
            item_id=item_id,
            config_name="Baseline-RAG",
            status=status,
            time_ms=elapsed_ms,
            urc_flag=0,  # No transformation, no URC
            raw_ast=raw_ast,
            final_ast=raw_ast,
            error_message=verify_result.get("message", "")
        )


class SAPSEStrictPipeline(BasePipeline):
    """Pipeline 2: SAPSE-Strict (VC-only).

    Verified Core only, with AdmissibleSpec gatekeeper.
    Demonstrates safety but poor coverage.
    """

    def process_item(self, item_id: str, raw_ast: str) -> PipelineResult:
        """Process item: check admissible -> VC passes -> verify.

        Args:
            item_id: Item identifier
            raw_ast: Raw AST from RAG

        Returns:
            PipelineResult
        """
        start_time = time.time()

        # Check admissibility
        is_admissible, failures = check_admissible_spec(raw_ast)

        if not is_admissible:
            # Abstain
            elapsed_ms = (time.time() - start_time) * 1000
            return PipelineResult(
                item_id=item_id,
                config_name="SAPSE-Strict",
                status="Abstained",
                time_ms=elapsed_ms,
                urc_flag=0,
                raw_ast=raw_ast,
                final_ast=raw_ast,
                admissibility_failures=failures
            )

        # Apply VC passes
        final_ast = apply_verified_core_passes(raw_ast)

        # Verify
        verify_result = self.verifier_fn(final_ast)
        status = "Verified" if verify_result["status"] == "passed" else "Failed"

        elapsed_ms = (time.time() - start_time) * 1000

        return PipelineResult(
            item_id=item_id,
            config_name="SAPSE-Strict",
            status=status,
            time_ms=elapsed_ms,
            urc_flag=0,  # VC passes are verified, no URC
            raw_ast=raw_ast,
            final_ast=final_ast,
            error_message=verify_result.get("message", "")
        )


class SAPSEFastPipeline(BasePipeline):
    """Pipeline 3: SAPSE-Fast (UP-only).

    Utility Passes only, no guards.
    Improves coverage but may produce unsafe verified lemmas (URC > 0).
    """

    def process_item(self, item_id: str, raw_ast: str) -> PipelineResult:
        """Process item: UP passes -> verify -> URC check.

        Args:
            item_id: Item identifier
            raw_ast: Raw AST from RAG

        Returns:
            PipelineResult with URC flag
        """
        start_time = time.time()

        # Apply VC passes first (Pass 1, 3 are relatively safe)
        ast_p1 = run_pass_1_require(raw_ast)
        ast_p3 = run_pass_3_eq_canonical(ast_p1)

        # Apply UP passes (Pass 4, 5, 6 - heuristic)
        ast_p4 = run_pass_4_scope(ast_p3)
        ast_p5 = run_pass_5_list(ast_p4)
        final_ast = run_pass_6_reformat(ast_p5)

        # Verify
        verify_result = self.verifier_fn(final_ast)
        status = "Verified" if verify_result["status"] == "passed" else "Failed"

        # Check for URC if verified
        urc_flag = 0
        if status == "Verified":
            is_urc = find_suspicious_edit(raw_ast, final_ast)
            urc_flag = 1 if is_urc else 0

        elapsed_ms = (time.time() - start_time) * 1000

        return PipelineResult(
            item_id=item_id,
            config_name="SAPSE-Fast",
            status=status,
            time_ms=elapsed_ms,
            urc_flag=urc_flag,
            raw_ast=raw_ast,
            final_ast=final_ast,
            error_message=verify_result.get("message", "")
        )


class SAPSESynergyPipeline(BasePipeline):
    """Pipeline 4: SAPSE-Synergy (UP + VC).

    Combines UP for preprocessing with VC gatekeeper for safety.
    Demonstrates synergy: UP improves coverage, VC ensures safety.
    """

    def process_item(self, item_id: str, raw_ast: str) -> PipelineResult:
        """Process item: UP preprocessing -> check admissible -> VC passes -> verify.

        Args:
            item_id: Item identifier
            raw_ast: Raw AST from RAG

        Returns:
            PipelineResult
        """
        start_time = time.time()

        # Pre-processing with Utility Passes
        pre_processed_ast = run_pass_6_reformat(
            run_pass_5_list(
                run_pass_4_scope(raw_ast)
            )
        )

        # Guarded verification with VC
        is_admissible, failures = check_admissible_spec(pre_processed_ast)

        if not is_admissible:
            # Abstain
            elapsed_ms = (time.time() - start_time) * 1000
            return PipelineResult(
                item_id=item_id,
                config_name="SAPSE-Synergy",
                status="Abstained",
                time_ms=elapsed_ms,
                urc_flag=0,
                raw_ast=raw_ast,
                final_ast=pre_processed_ast,
                admissibility_failures=failures
            )

        # Apply VC passes
        final_ast = run_pass_3_eq_canonical(
            run_pass_1_require(pre_processed_ast)
        )

        # Verify
        verify_result = self.verifier_fn(final_ast)
        status = "Verified" if verify_result["status"] == "passed" else "Failed"

        elapsed_ms = (time.time() - start_time) * 1000

        return PipelineResult(
            item_id=item_id,
            config_name="SAPSE-Synergy",
            status=status,
            time_ms=elapsed_ms,
            urc_flag=0,  # VC gatekeeper ensures no URC
            raw_ast=raw_ast,
            final_ast=final_ast,
            error_message=verify_result.get("message", "")
        )


# ============================================================================
# Pipeline Factory
# ============================================================================

def create_pipeline(pipeline_name: str, verifier_fn) -> BasePipeline:
    """Factory function to create pipeline instances.

    Args:
        pipeline_name: One of {"Baseline-RAG", "SAPSE-Strict", "SAPSE-Fast", "SAPSE-Synergy"}
        verifier_fn: Verifier function

    Returns:
        Pipeline instance

    Raises:
        ValueError: If pipeline_name is invalid
    """
    pipelines = {
        "Baseline-RAG": BaselineRAGPipeline,
        "SAPSE-Strict": SAPSEStrictPipeline,
        "SAPSE-Fast": SAPSEFastPipeline,
        "SAPSE-Synergy": SAPSESynergyPipeline,
    }

    if pipeline_name not in pipelines:
        raise ValueError(f"Unknown pipeline: {pipeline_name}. "
                        f"Choose from {list(pipelines.keys())}")

    return pipelines[pipeline_name](verifier_fn)
