"""Coq verification using coqc."""

import subprocess
import tempfile
from pathlib import Path
from typing import Dict, Literal

from loguru import logger

VerificationResult = Literal["passed", "failed", "fixable", "error"]


class CoqVerifier:
    """
    Verifies Coq lemmas using coqc compiler.

    Example:
        >>> verifier = CoqVerifier()
        >>> result = verifier.verify("Lemma test: True. Proof. trivial. Qed.")
        >>> result["status"]
        'passed'
    """

    def __init__(self, coqc_path: str = "coqc", timeout: int = 30, random_seed: int = 0):
        """
        Initialize Coq verifier.

        Args:
            coqc_path: Path to coqc binary.
            timeout: Verification timeout in seconds.
            random_seed: Random seed for Coq proof search (default: 0).
        """
        self.coqc_path = coqc_path
        self.timeout = timeout
        self.random_seed = random_seed
        self.available = self._check_coqc_available()

        if self.available:
            logger.info(f"Initialized CoqVerifier with coqc at {coqc_path}, random_seed={random_seed}")
        else:
            logger.warning("coqc not available, verification will fail")

    def _check_coqc_available(self) -> bool:
        """Check if coqc is available."""
        try:
            result = subprocess.run(
                [self.coqc_path, "--version"],
                capture_output=True,
                timeout=5,
            )
            return result.returncode == 0
        except Exception:
            return False

    def verify(self, coq_code: str) -> Dict[str, any]:
        """
        Verify a Coq code snippet.

        Args:
            coq_code: Coq lemma and proof text.

        Returns:
            Dict with 'status', 'message', 'stdout', 'stderr' keys.

        Example:
            >>> result = verifier.verify("Lemma x: forall n, n = n. Proof. reflexivity. Qed.")
            >>> result["status"]
            'passed'
        """
        if not self.available:
            return {
                "status": "error",
                "message": "coqc not available",
                "stdout": "",
                "stderr": "",
            }

        # Create temporary file
        with tempfile.NamedTemporaryFile(
            mode="w",
            suffix=".v",
            delete=False,
            encoding="utf-8",
        ) as f:
            # Inject random seed at the beginning if non-zero
            if self.random_seed != 0:
                f.write(f"Set Random Seed {self.random_seed}.\n\n")
            f.write(coq_code)
            temp_path = f.name

        try:
            # Run coqc
            result = subprocess.run(
                [self.coqc_path, temp_path],
                capture_output=True,
                text=True,
                timeout=self.timeout,
            )

            stdout = result.stdout
            stderr = result.stderr

            if result.returncode == 0:
                status = "passed"
                message = "Verification successful"
            else:
                # Analyze error to determine if fixable
                if self._is_fixable_error(stderr):
                    status = "fixable"
                    message = "Verification failed but may be fixable"
                else:
                    status = "failed"
                    message = "Verification failed"

            return {
                "status": status,
                "message": message,
                "stdout": stdout,
                "stderr": stderr,
            }

        except subprocess.TimeoutExpired:
            return {
                "status": "error",
                "message": f"Verification timeout after {self.timeout}s",
                "stdout": "",
                "stderr": "",
            }

        except Exception as e:
            return {
                "status": "error",
                "message": f"Verification error: {str(e)}",
                "stdout": "",
                "stderr": "",
            }

        finally:
            # Clean up temporary files
            Path(temp_path).unlink(missing_ok=True)
            Path(temp_path).with_suffix(".vo").unlink(missing_ok=True)
            Path(temp_path).with_suffix(".vok").unlink(missing_ok=True)
            Path(temp_path).with_suffix(".vos").unlink(missing_ok=True)
            Path(temp_path).with_suffix(".glob").unlink(missing_ok=True)

    def _is_fixable_error(self, error_message: str) -> bool:
        """
        Determine if an error is potentially fixable.

        Args:
            error_message: Coq error output.

        Returns:
            True if error appears fixable.
        """
        fixable_patterns = [
            "undeclared",
            "not found",
            "syntax error",
            "unbound",
            "expected",
        ]

        error_lower = error_message.lower()
        return any(pattern in error_lower for pattern in fixable_patterns)

    def batch_verify(self, coq_codes: list[str]) -> list[Dict]:
        """
        Verify multiple Coq snippets.

        Args:
            coq_codes: List of Coq code strings.

        Returns:
            List of verification result dicts.

        Example:
            >>> results = verifier.batch_verify(lemma_drafts)
            >>> passed = sum(1 for r in results if r["status"] == "passed")
        """
        results = []
        for i, code in enumerate(coq_codes):
            logger.debug(f"Verifying lemma {i + 1}/{len(coq_codes)}")
            result = self.verify(code)
            results.append(result)

        logger.info(
            f"Batch verification complete: {len(results)} lemmas verified"
        )
        return results
