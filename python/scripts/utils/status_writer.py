"""Status snapshot writer for experiment monitoring.

Writes periodic JSON snapshots of experiment progress to enable
real-time monitoring without waiting for final results.
"""

import json
from datetime import datetime
from pathlib import Path
from typing import Dict, Optional


class StatusWriter:
    """Writes experiment status snapshots to JSON.

    Example:
        >>> writer = StatusWriter("outputs/runs/D1/status.json")
        >>> writer.update(phase="generation", completed_proofs=100, generated_lemmas=1500)
        >>> writer.write()
    """

    def __init__(self, output_path: str):
        """Initialize status writer.

        Args:
            output_path: Path to write status.json file.
        """
        self.output_path = Path(output_path)
        self.output_path.parent.mkdir(parents=True, exist_ok=True)

        self.status = {
            "ts": datetime.now().isoformat(),
            "phase": "init",
            "completed_proofs": 0,
            "generated_lemmas": 0,
            "verified": 0,
            "fixable": 0,
            "failed": 0,
            "pass_rate": 0.0,
            "eta_note": ""
        }

    def update(
        self,
        phase: Optional[str] = None,
        completed_proofs: Optional[int] = None,
        generated_lemmas: Optional[int] = None,
        verified: Optional[int] = None,
        fixable: Optional[int] = None,
        failed: Optional[int] = None,
        eta_note: Optional[str] = None
    ):
        """Update status fields.

        Args:
            phase: Current phase ('generation', 'dedup', 'verification', 'complete').
            completed_proofs: Number of proofs processed.
            generated_lemmas: Number of lemmas generated.
            verified: Number of lemmas verified as passed.
            fixable: Number of lemmas marked as fixable.
            failed: Number of lemmas that failed verification.
            eta_note: Human-readable ETA note.
        """
        self.status["ts"] = datetime.now().isoformat()

        if phase is not None:
            self.status["phase"] = phase
        if completed_proofs is not None:
            self.status["completed_proofs"] = completed_proofs
        if generated_lemmas is not None:
            self.status["generated_lemmas"] = generated_lemmas
        if verified is not None:
            self.status["verified"] = verified
        if fixable is not None:
            self.status["fixable"] = fixable
        if failed is not None:
            self.status["failed"] = failed
        if eta_note is not None:
            self.status["eta_note"] = eta_note

        # Calculate pass rate
        total_verified = self.status["verified"] + self.status["fixable"] + self.status["failed"]
        if total_verified > 0:
            self.status["pass_rate"] = self.status["verified"] / total_verified
        else:
            self.status["pass_rate"] = 0.0

    def write(self):
        """Write current status to JSON file."""
        with open(self.output_path, 'w') as f:
            json.dump(self.status, f, indent=2)

    def read(self) -> Dict:
        """Read current status from JSON file.

        Returns:
            Status dictionary.
        """
        if self.output_path.exists():
            with open(self.output_path) as f:
                return json.load(f)
        return self.status


def create_status_writer(run_dir: str) -> StatusWriter:
    """Convenience function to create a status writer for a run.

    Args:
        run_dir: Run directory path (e.g., 'outputs/runs/D1').

    Returns:
        Configured StatusWriter instance.

    Example:
        >>> writer = create_status_writer("outputs/runs/D1_e5_rag_best")
        >>> writer.update(phase="generation", completed_proofs=50)
        >>> writer.write()
    """
    status_path = Path(run_dir) / "status.json"
    return StatusWriter(str(status_path))


if __name__ == "__main__":
    # Test the status writer
    import tempfile
    import os

    with tempfile.TemporaryDirectory() as tmpdir:
        writer = StatusWriter(os.path.join(tmpdir, "test_status.json"))

        # Simulate progress
        writer.update(phase="generation", completed_proofs=100, generated_lemmas=1500)
        writer.write()

        writer.update(phase="dedup", completed_proofs=100, generated_lemmas=1200)
        writer.write()

        writer.update(
            phase="verification",
            completed_proofs=100,
            generated_lemmas=1200,
            verified=200,
            fixable=700,
            failed=300
        )
        writer.write()

        # Read back
        status = writer.read()
        print(json.dumps(status, indent=2))
        assert status["phase"] == "verification"
        assert status["pass_rate"] > 0
        print("✓ StatusWriter test passed!")
