"""Checkpoint management for pause/resume functionality."""

import json
import pickle
from pathlib import Path
from typing import Any, Dict, List, Optional
from datetime import datetime

from loguru import logger


class CheckpointManager:
    """
    Manages checkpointing for long-running experiments.
    
    Allows pausing and resuming experiments without losing progress.
    
    Example:
        >>> manager = CheckpointManager("outputs/runs/C1_deepseek_rag")
        >>> manager.save_checkpoint(processed_count=100, results=[...])
        >>> state = manager.load_checkpoint()
    """
    
    def __init__(self, run_dir: str):
        """
        Initialize checkpoint manager.
        
        Args:
            run_dir: Directory for this experiment run.
        """
        self.run_dir = Path(run_dir)
        self.run_dir.mkdir(parents=True, exist_ok=True)
        
        self.checkpoint_file = self.run_dir / "checkpoint.pkl"
        self.metadata_file = self.run_dir / "checkpoint_metadata.json"
        self.progress_file = self.run_dir / "progress.jsonl"
        
    def save_checkpoint(
        self,
        processed_proofs: List[str],
        current_results: List[Dict[str, Any]],
        metrics: Dict[str, Any],
        last_proof_id: Optional[str] = None,
        additional_state: Optional[Dict] = None
    ) -> None:
        """
        Save checkpoint with current progress.
        
        Args:
            processed_proofs: List of proof IDs already processed.
            current_results: All results generated so far.
            metrics: Current metrics state.
            last_proof_id: ID of last processed proof.
            additional_state: Any additional state to save.
        """
        checkpoint_data = {
            "processed_proofs": processed_proofs,
            "current_results": current_results,
            "metrics": metrics,
            "last_proof_id": last_proof_id,
            "additional_state": additional_state or {},
            "timestamp": datetime.now().isoformat(),
            "checkpoint_version": "1.0"
        }
        
        # Save binary checkpoint
        with open(self.checkpoint_file, "wb") as f:
            pickle.dump(checkpoint_data, f)
            
        # Save human-readable metadata
        metadata = {
            "timestamp": checkpoint_data["timestamp"],
            "processed_count": len(processed_proofs),
            "results_count": len(current_results),
            "last_proof_id": last_proof_id,
            "checkpoint_file": str(self.checkpoint_file)
        }
        
        with open(self.metadata_file, "w") as f:
            json.dump(metadata, f, indent=2)
            
        logger.info(
            f"Checkpoint saved: {len(processed_proofs)} proofs, "
            f"{len(current_results)} results"
        )
        
    def load_checkpoint(self) -> Optional[Dict[str, Any]]:
        """
        Load checkpoint if it exists.
        
        Returns:
            Checkpoint data dictionary or None if no checkpoint exists.
        """
        if not self.checkpoint_file.exists():
            logger.info("No checkpoint found - starting from beginning")
            return None
            
        try:
            with open(self.checkpoint_file, "rb") as f:
                checkpoint_data = pickle.load(f)
                
            logger.info(
                f"Checkpoint loaded: {len(checkpoint_data['processed_proofs'])} "
                f"proofs already processed"
            )
            
            return checkpoint_data
            
        except Exception as e:
            logger.error(f"Failed to load checkpoint: {e}")
            logger.warning("Starting from beginning")
            return None
            
    def log_progress(self, proof_id: str, step_count: int, result_count: int) -> None:
        """
        Log progress to append-only file for monitoring.
        
        Args:
            proof_id: Current proof being processed.
            step_count: Number of steps in this proof.
            result_count: Total results generated so far.
        """
        progress_entry = {
            "timestamp": datetime.now().isoformat(),
            "proof_id": proof_id,
            "step_count": step_count,
            "result_count": result_count
        }
        
        with open(self.progress_file, "a") as f:
            f.write(json.dumps(progress_entry) + "\n")
            
    def clear_checkpoint(self) -> None:
        """Clear checkpoint files (e.g., after successful completion)."""
        if self.checkpoint_file.exists():
            self.checkpoint_file.unlink()
        if self.metadata_file.exists():
            self.metadata_file.unlink()
        logger.info("Checkpoint cleared")
        
    def checkpoint_exists(self) -> bool:
        """Check if a checkpoint exists."""
        return self.checkpoint_file.exists()
        
    def get_checkpoint_info(self) -> Optional[Dict[str, Any]]:
        """Get checkpoint metadata without loading full checkpoint."""
        if not self.metadata_file.exists():
            return None
            
        try:
            with open(self.metadata_file, "r") as f:
                return json.load(f)
        except Exception as e:
            logger.error(f"Failed to read checkpoint metadata: {e}")
            return None
