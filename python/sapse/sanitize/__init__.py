"""AST-based sanitizer with admissibility guards."""

from .sanitizer import Sanitizer, SanitizerConfig, SanitizerResult
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
from .pipelines import (
    BasePipeline,
    BaselineRAGPipeline,
    SAPSEStrictPipeline,
    SAPSEFastPipeline,
    SAPSESynergyPipeline,
    PipelineResult,
    create_pipeline,
)

__all__ = [
    "Sanitizer",
    "SanitizerConfig",
    "SanitizerResult",
    "run_pass_1_require",
    "run_pass_2_binder_identity",
    "run_pass_3_eq_canonical",
    "run_pass_4_scope",
    "run_pass_5_list",
    "run_pass_6_reformat",
    "check_admissible_spec",
    "find_suspicious_edit",
    "apply_utility_passes",
    "apply_verified_core_passes",
    "BasePipeline",
    "BaselineRAGPipeline",
    "SAPSEStrictPipeline",
    "SAPSEFastPipeline",
    "SAPSESynergyPipeline",
    "PipelineResult",
    "create_pipeline",
]
