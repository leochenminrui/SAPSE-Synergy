"""Atomic checkpoint manager with pause/resume."""

import json
import time
import hashlib
import signal
from pathlib import Path
from typing import Optional, Dict, Any, List
from loguru import logger


class CheckpointManager:
    """Manages atomic checkpoints with .tmp + rename."""

    def __init__(self, run_dir: Path, config: Dict[str, Any], seed: int = 1):
        self.run_dir = Path(run_dir)
        self.run_dir.mkdir(parents=True, exist_ok=True)
        self.config = config
        self.seed = seed
        self.config_hash = self._hash_config(config)
        self.last_checkpoint_time = time.time()
        self.interrupted = False

        self.state_path = self.run_dir / "state.jsonl"
        self.checkpoint_path = self.run_dir / "checkpoint.json"
        self.manifest_path = self.run_dir / "manifest.json"
        self.partial_results_path = self.run_dir / "partial_results.jsonl"
        self.metrics_path = self.run_dir / "metrics_partial.json"

        # Register signal handlers
        signal.signal(signal.SIGINT, self._handle_interrupt)
        signal.signal(signal.SIGTERM, self._handle_interrupt)

    def _hash_config(self, config: Dict[str, Any]) -> str:
        """Generate deterministic config hash."""
        config_str = json.dumps(config, sort_keys=True)
        return hashlib.sha256(config_str.encode()).hexdigest()[:12]

    def _handle_interrupt(self, signum, frame):
        """Handle SIGINT/SIGTERM gracefully."""
        logger.warning(f"Received signal {signum}, will checkpoint and exit...")
        self.interrupted = True

    def append_item_state(self, item_state: Dict[str, Any]):
        """Append item state to WAL (atomic)."""
        tmp_path = self.state_path.with_suffix('.jsonl.tmp')

        # Copy existing state to temp, then append new item
        if self.state_path.exists():
            with open(self.state_path, 'r') as src, open(tmp_path, 'w') as dst:
                for line in src:
                    dst.write(line)
                dst.write(json.dumps(item_state) + '\n')
        else:
            # First item - create new file
            with open(tmp_path, 'w') as f:
                f.write(json.dumps(item_state) + '\n')

        # Atomic rename
        tmp_path.replace(self.state_path)

    def write_checkpoint(self, run_state: Dict[str, Any]):
        """Write checkpoint atomically."""
        tmp_path = self.checkpoint_path.with_suffix('.json.tmp')
        with open(tmp_path, 'w') as f:
            json.dump(run_state, f, indent=2)
        tmp_path.replace(self.checkpoint_path)
        self.last_checkpoint_time = time.time()
        logger.info(f"Checkpoint written: {run_state['verified_count']}/{run_state['total_count']} items")

    def should_checkpoint(self, item_count: int) -> bool:
        """Check if checkpoint is due (every 50 items or 60s)."""
        elapsed = time.time() - self.last_checkpoint_time
        return (item_count % 50 == 0) or (elapsed >= 60)

    def load_checkpoint(self) -> Optional[Dict[str, Any]]:
        """Load existing checkpoint if available."""
        if self.checkpoint_path.exists():
            with open(self.checkpoint_path) as f:
                ckpt = json.load(f)
                logger.info(f"Loaded checkpoint: {ckpt.get('run_id')}, cursor={ckpt.get('queue_cursor')}")
                return ckpt
        return None

    def load_processed_ids(self) -> set:
        """Load set of already-processed item IDs from state.jsonl."""
        processed = set()
        if self.state_path.exists():
            with open(self.state_path) as f:
                for line in f:
                    if line.strip():
                        item = json.loads(line)
                        processed.add(item.get('item_id'))
            logger.info(f"Loaded {len(processed)} processed items from state log")
        return processed

    def write_manifest(self, commit_hash: str, config_path: str):
        """Write run manifest."""
        manifest = {
            "run_id": self.run_dir.name,
            "commit_hash": commit_hash,
            "config_path": config_path,
            "config_hash": self.config_hash,
            "seed": self.seed,
            "timestamp": time.time()
        }
        with open(self.manifest_path, 'w') as f:
            json.dump(manifest, f, indent=2)
        logger.info(f"Manifest written: {self.run_dir.name}")

    def append_partial_result(self, result: Dict[str, Any]):
        """Append partial result (dedup candidate or sanitizer outcome)."""
        tmp_path = self.partial_results_path.with_suffix('.jsonl.tmp')
        mode = 'a' if self.partial_results_path.exists() else 'w'
        with open(tmp_path, mode) as f:
            f.write(json.dumps(result) + '\n')
        tmp_path.replace(self.partial_results_path)

    def write_metrics(self, metrics: Dict[str, Any]):
        """Write partial metrics."""
        tmp_path = self.metrics_path.with_suffix('.json.tmp')
        with open(tmp_path, 'w') as f:
            json.dump(metrics, f, indent=2)
        tmp_path.replace(self.metrics_path)
