"""Mock verifier for testing without Coq installation."""

import random
import re
from typing import Dict

from loguru import logger


class MockVerifier:
    """
    Mock Coq verifier for testing and development.

    Simulates verification based on simple heuristics.

    Example:
        >>> verifier = MockVerifier(pass_rate=0.8)
        >>> result = verifier.verify("Lemma test: True. Proof. trivial. Qed.")
        >>> result["status"] in ["passed", "failed", "fixable"]
        True
    """

    def __init__(
        self,
        pass_rate: float = 0.7,
        fixable_rate: float = 0.2,
        random_seed: int = None,
    ):
        """
        Initialize mock verifier.

        Args:
            pass_rate: Probability of passing verification (0-1).
            fixable_rate: Probability of fixable errors (0-1).
            random_seed: Random seed for reproducibility.
        """
        self.pass_rate = pass_rate
        self.fixable_rate = fixable_rate

        if random_seed is not None:
            random.seed(random_seed)

        logger.info(
            f"Initialized MockVerifier (pass_rate={pass_rate}, fixable_rate={fixable_rate})"
        )

    def verify(self, coq_code: str) -> Dict[str, any]:
        """
        Mock verification of Coq code.

        Args:
            coq_code: Coq lemma text.

        Returns:
            Dict with 'status', 'message', 'stdout', 'stderr' keys.

        Example:
            >>> result = verifier.verify("Lemma x: True.")
            >>> result["status"]
        """
        # Simple heuristics
        has_lemma = bool(
            re.search(r"\b(Lemma|Theorem|Proposition|Corollary)\b", coq_code)
        )
        has_proof = "Proof" in coq_code or "proof" in coq_code
        has_qed = "Qed" in coq_code or "Defined" in coq_code

        # Determine status based on heuristics and randomness
        if not has_lemma:
            status = "failed"
            message = "No lemma declaration found"
        elif has_lemma and has_proof and has_qed:
            # Well-formed, use pass rate
            rand_val = random.random()
            if rand_val < self.pass_rate:
                status = "passed"
                message = "Mock verification successful"
            elif rand_val < self.pass_rate + self.fixable_rate:
                status = "fixable"
                message = "Mock verification failed (fixable)"
            else:
                status = "failed"
                message = "Mock verification failed"
        else:
            # Incomplete, likely fixable
            if random.random() < self.fixable_rate:
                status = "fixable"
                message = "Incomplete proof (fixable)"
            else:
                status = "failed"
                message = "Incomplete proof"

        return {
            "status": status,
            "message": message,
            "stdout": f"Mock stdout for: {coq_code[:30]}...",
            "stderr": "" if status == "passed" else f"Mock error: {message}",
        }

    def batch_verify(self, coq_codes: list[str]) -> list[Dict]:
        """
        Mock batch verification.

        Args:
            coq_codes: List of Coq code strings.

        Returns:
            List of verification result dicts.

        Example:
            >>> results = verifier.batch_verify(lemmas)
        """
        results = [self.verify(code) for code in coq_codes]
        logger.info(f"Mock batch verification: {len(results)} lemmas")
        return results


def create_verifier(use_mock: bool = False, **kwargs):
    """
    Factory function to create appropriate verifier.

    Args:
        use_mock: If True, use MockVerifier. Otherwise try CoqVerifier.
        **kwargs: Arguments for verifier constructor.

    Returns:
        Verifier instance (CoqVerifier or MockVerifier).

    Example:
        >>> verifier = create_verifier(use_mock=True, pass_rate=0.8)
        >>> verifier = create_verifier(use_mock=False, coqc_path="/usr/bin/coqc")
    """
    if use_mock:
        # Filter kwargs for MockVerifier
        mock_kwargs = {
            k: v for k, v in kwargs.items()
            if k in ['pass_rate', 'fixable_rate', 'random_seed']
        }
        return MockVerifier(**mock_kwargs)
    else:
        try:
            from .coq_verify import CoqVerifier

            # Filter kwargs for CoqVerifier
            coq_kwargs = {
                k: v for k, v in kwargs.items()
                if k in ['coqc_path', 'timeout', 'coq_lib_path', 'random_seed']
            }
            verifier = CoqVerifier(**coq_kwargs)
            if not verifier.available:
                logger.warning("Coq not available, falling back to MockVerifier")
                return MockVerifier()
            return verifier
        except Exception as e:
            logger.warning(f"Could not create CoqVerifier: {e}, using MockVerifier")
            return MockVerifier()
