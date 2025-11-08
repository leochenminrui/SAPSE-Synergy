"""Coq lemma I/O utilities."""

import re
from typing import Dict, List, Optional

from loguru import logger


class CoqLemmaParser:
    """
    Parser for Coq lemmas and theorems.

    Extracts lemma names, statements, and metadata.

    Example:
        >>> parser = CoqLemmaParser()
        >>> lemma = parser.parse_lemma("Lemma plus_comm: forall a b, a + b = b + a.")
        >>> lemma["name"]
        'plus_comm'
    """

    def parse_lemma(self, coq_text: str) -> Optional[Dict[str, str]]:
        """
        Parse a Coq lemma from text.

        Args:
            coq_text: Coq lemma text.

        Returns:
            Dictionary with 'name', 'statement', 'full_text' keys, or None if parsing fails.

        Example:
            >>> lemma = parser.parse_lemma("Lemma test: forall x, x = x.")
            >>> lemma["name"]
            'test'
        """
        # Try to extract lemma/theorem name and statement
        patterns = [
            r"(?:Lemma|Theorem|Proposition|Corollary)\s+(\w+)\s*:(.+?)(?:\.|$)",
            r"(\w+)\s*:(.+?)(?:\.|$)",
        ]

        for pattern in patterns:
            match = re.search(pattern, coq_text, re.DOTALL)
            if match:
                name = match.group(1).strip()
                statement = match.group(2).strip()
                return {
                    "name": name,
                    "statement": statement,
                    "full_text": coq_text.strip(),
                }

        logger.warning(f"Could not parse Coq lemma: {coq_text[:50]}...")
        return None

    def format_lemma(self, lemma_dict: Dict[str, str]) -> str:
        """
        Format a lemma dictionary as Coq text.

        Args:
            lemma_dict: Dictionary with 'name' and 'statement' or 'full_text'.

        Returns:
            Formatted Coq lemma text.

        Example:
            >>> lemma = {"name": "test", "statement": "forall x, x = x"}
            >>> parser.format_lemma(lemma)
            'Lemma test: forall x, x = x.'
        """
        if "full_text" in lemma_dict:
            return lemma_dict["full_text"]

        name = lemma_dict.get("name", "unnamed")
        statement = lemma_dict.get("statement", "")

        return f"Lemma {name}: {statement}."

    def extract_dependencies(self, coq_text: str) -> List[str]:
        """
        Extract lemma dependencies from Coq proof text.

        Args:
            coq_text: Coq proof text.

        Returns:
            List of lemma names referenced in the proof.

        Example:
            >>> deps = parser.extract_dependencies("apply plus_comm. rewrite mult_1.")
            >>> "plus_comm" in deps
            True
        """
        # Find common tactics that reference lemmas
        tactics = [
            r"apply\s+(\w+)",
            r"rewrite\s+(\w+)",
            r"exact\s+(\w+)",
            r"pose\s+proof\s+(\w+)",
        ]

        dependencies = set()
        for tactic in tactics:
            matches = re.findall(tactic, coq_text)
            dependencies.update(matches)

        return sorted(list(dependencies))
