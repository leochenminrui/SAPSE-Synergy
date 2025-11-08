"""Natural language proof I/O utilities."""

import re
from typing import Dict, List

from loguru import logger


class NLProofParser:
    """
    Parser for natural-language proofs.

    Extracts individual proof steps from NL proofs.

    Example:
        >>> parser = NLProofParser()
        >>> steps = parser.extract_steps(nl_proof)
        >>> for step in steps:
        ...     print(step["text"])
    """

    def __init__(self, step_separator: str = r"Step\s*\d+:"):
        """
        Initialize NL proof parser.

        Args:
            step_separator: Regex pattern for detecting proof steps.
        """
        self.step_separator = step_separator

    def extract_steps(self, nl_proof: str) -> List[Dict[str, str]]:
        """
        Extract individual steps from natural language proof.

        Args:
            nl_proof: Natural language proof text.

        Returns:
            List of proof steps with metadata.

        Example:
            >>> proof = "Step1: Use induction. Step2: Apply lemma."
            >>> steps = parser.extract_steps(proof)
            >>> len(steps)
            2
        """
        # Split by step pattern
        parts = re.split(f"({self.step_separator})", nl_proof)

        steps = []
        step_num = 0

        for i in range(1, len(parts), 2):
            if i + 1 < len(parts):
                step_header = parts[i].strip()
                step_text = parts[i + 1].strip()

                if step_text:
                    step_num += 1
                    steps.append(
                        {
                            "step_num": step_num,
                            "header": step_header,
                            "text": step_text,
                        }
                    )

        # If no steps detected, treat entire proof as single step
        if not steps and nl_proof.strip():
            steps.append(
                {
                    "step_num": 1,
                    "header": "Step 1:",
                    "text": nl_proof.strip(),
                }
            )

        logger.debug(f"Extracted {len(steps)} steps from NL proof")
        return steps

    def format_step(self, step: Dict[str, str]) -> str:
        """
        Format a proof step as a string.

        Args:
            step: Step dictionary with 'header' and 'text' keys.

        Returns:
            Formatted step string.

        Example:
            >>> step = {"header": "Step 1:", "text": "By induction"}
            >>> parser.format_step(step)
            'Step 1: By induction'
        """
        return f"{step.get('header', '')} {step.get('text', '')}".strip()
