"""State models for checkpointing."""

from dataclasses import dataclass, asdict, field
from typing import Optional, Dict, Any
import json


@dataclass
class ItemState:
    """Per-item processing state."""
    item_id: str
    retrieved_k: int
    sim_threshold: float
    dedup_threshold: float
    pass_name: Optional[str] = None
    admissible: Optional[bool] = None
    applied: Optional[bool] = None
    abstain: bool = False
    would_abstain_if_checked: bool = False
    final_status: str = "pending"
    verifier: str = "coq"
    timestamp_start: float = 0.0
    timestamp_end: float = 0.0
    failure_type: Optional[str] = None
    unsafe_rewrite_count: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class RunState:
    """Global run state."""
    run_id: str
    config_hash: str
    last_processed_id: str
    queue_cursor: int
    seed: int
    timestamp_start: float
    timestamp_last_checkpoint: float
    verified_count: int = 0
    total_count: int = 0
    abstain_count: int = 0
    attempted_count: int = 0
    type_fail_count: int = 0
    admissible_count: int = 0
    sound_repairs_count: int = 0
    unique_verified_count: int = 0
    rescued_count: int = 0  # Hybrid mode only
    failure_counts: Dict[str, int] = field(default_factory=lambda: {
        "type": 0,
        "syntax": 0,
        "proof": 0,
        "timeout": 0,
        "other": 0
    })

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)
