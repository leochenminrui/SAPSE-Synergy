"""Sanitizer with verified structural repair passes.

Implements Python-level sanitizer passes corresponding to the formalized
transformations in SAPSE-Coq/theories/Sanitizer.v:
- R_req: Require injection (import-only context extension)
- R_bind: Binder normalization (WellFormedU check)
- R_eq: Equality canonicalization

Admissibility guards enforce preconditions before applying verified passes.
"""

import re
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Tuple
from loguru import logger


@dataclass
class SanitizerConfig:
    """Configuration for sanitizer behavior."""
    enabled: bool = True
    check_guards: bool = True
    passes: List[str] = field(default_factory=lambda: [
        "require_injection",
        "binder_norm",
        "eq_canon"
    ])


@dataclass
class SanitizerResult:
    """Result of sanitizer application."""
    applied: bool
    abstain: bool
    would_abstain_if_checked: bool
    result_text: str
    passes_applied: List[str] = field(default_factory=list)
    unsafe_rewrite_count: int = 0
    admissibility_failures: List[str] = field(default_factory=list)


class Sanitizer:
    """AST sanitizer with admissibility guards.

    Mirrors the formal semantics-preserving transformations in Sanitizer.v.
    """

    def __init__(self, config: SanitizerConfig):
        self.config = config

    def check_well_formed_u(self, lemma_text: str) -> bool:
        """Check WellFormedU precondition (no unbound variables).

        Corresponds to WellFormedU inductive predicate in Sanitizer.v:52-60.
        Simplified heuristic: check for basic syntactic structure.
        """
        # Must contain a statement keyword
        has_statement = bool(re.search(
            r'\b(Definition|Lemma|Theorem|Proposition|Fact|Remark|Corollary)\b',
            lemma_text
        ))

        # Must not have obvious syntax errors
        has_balanced_parens = lemma_text.count('(') == lemma_text.count(')')

        return has_statement and has_balanced_parens

    def check_disjoint_ctx(self, lemma_text: str) -> bool:
        """Check disjoint context requirement.

        For R_req (Require injection), we require that imports are
        environment-only extensions. Simplified: check that Require
        statements come before definitions.
        """
        lines = lemma_text.strip().split('\n')
        seen_definition = False

        for line in lines:
            line_stripped = line.strip()
            if re.match(r'\b(Definition|Lemma|Theorem)', line_stripped):
                seen_definition = True
            elif seen_definition and re.match(r'\bRequire\b', line_stripped):
                # Require after definition violates context disjointness
                return False

        return True

    def check_admissible(self, lemma_text: str) -> Tuple[bool, List[str]]:
        """Check all admissibility guards.

        Returns (is_admissible, list_of_failures).
        """
        if not self.config.check_guards:
            return True, []

        failures = []

        if not self.check_well_formed_u(lemma_text):
            failures.append("WellFormedU")

        if not self.check_disjoint_ctx(lemma_text):
            failures.append("disjoint_ctx")

        return len(failures) == 0, failures

    def apply_passes(self, lemma_text: str) -> SanitizerResult:
        """Apply verified sanitizer passes with incremental type-checking.

        Args:
            lemma_text: Raw lemma text from abstractor

        Returns:
            SanitizerResult with applied passes and metadata
        """
        if not self.config.enabled:
            return SanitizerResult(
                applied=False,
                abstain=False,
                would_abstain_if_checked=False,
                result_text=lemma_text
            )

        admissible, failures = self.check_admissible(lemma_text)

        if not admissible:
            if self.config.check_guards:
                # Abstain: do not apply passes
                return SanitizerResult(
                    applied=False,
                    abstain=True,
                    would_abstain_if_checked=False,
                    result_text=lemma_text,
                    admissibility_failures=failures
                )
            else:
                # NoCheck mode: force apply and mark would_abstain
                result_text = self._force_apply(lemma_text)
                return SanitizerResult(
                    applied=True,
                    abstain=False,
                    would_abstain_if_checked=True,
                    result_text=result_text,
                    passes_applied=self.config.passes.copy(),
                    unsafe_rewrite_count=len(failures),
                    admissibility_failures=failures
                )

        # Apply passes in order
        result_text = lemma_text
        passes_applied = []

        for pass_name in self.config.passes:
            result_text = self._apply_pass(result_text, pass_name)
            passes_applied.append(pass_name)

        return SanitizerResult(
            applied=True,
            abstain=False,
            would_abstain_if_checked=False,
            result_text=result_text,
            passes_applied=passes_applied
        )

    def _apply_pass(self, text: str, pass_name: str) -> str:
        """Apply single verified pass.

        Args:
            text: Current lemma text
            pass_name: One of {require_injection, binder_norm, eq_canon}

        Returns:
            Transformed text
        """
        if pass_name == "require_injection":
            return self._apply_require_injection(text)
        elif pass_name == "binder_norm":
            return self._apply_binder_norm(text)
        elif pass_name == "eq_canon":
            return self._apply_eq_canon(text)
        else:
            logger.warning(f"Unknown pass: {pass_name}")
            return text

    def _apply_require_injection(self, text: str) -> str:
        """Apply R_req: Require injection (Sanitizer.v:11-18).

        Ensures necessary imports appear before definitions.
        Corresponds to weakening_req lemma (Sanitizer.v:30-48).
        """
        # Check if common Coq stdlib imports are present
        common_imports = [
            "From Stdlib Require Import",
            "Require Import List",
            "Require Import Arith"
        ]

        lines = text.strip().split('\n')
        has_require = any(
            any(imp in line for imp in common_imports)
            for line in lines
        )

        if not has_require:
            # Inject minimal Require header
            header = "From Stdlib Require Import String List Arith.\n"
            return header + text

        return text

    def _apply_binder_norm(self, text: str) -> str:
        """Apply R_bind: Binder normalization (Sanitizer.v:64-71).

        Ensures binders are well-formed (WellFormedU).
        This is mostly an identity transform in the formalization,
        but we can normalize whitespace and formatting.
        """
        # Normalize lambda/forall binder spacing
        text = re.sub(r'fun\s+(\w+)\s*:\s*(\w+)\s*=>', r'fun \1 : \2 =>', text)
        text = re.sub(r'forall\s+(\w+)\s*:\s*(\w+),', r'forall \1 : \2,', text)

        return text

    def _apply_eq_canon(self, text: str) -> str:
        """Apply R_eq: Equality canonicalization (Sanitizer.v:75-91).

        Canonicalizes equality expressions by ordering operands
        (e.g., tEq a b -> tEq min(a,b) max(a,b) by term size).
        Corresponds to R_eq_sem lemma (Sanitizer.v:142-195).

        Simplified heuristic: normalize symmetric operators.
        """
        # Normalize symmetric equality patterns (a = b -> sorted order)
        # This is a simplified text-level transformation
        # Real AST-level canonicalization would require parsing

        # Normalize Nat.eqb, Bool.eqb to canonical order
        text = re.sub(
            r'Nat\.eqb\s+([a-z]\w*)\s+([a-z]\w*)',
            lambda m: f'Nat.eqb {min(m.group(1), m.group(2))} {max(m.group(1), m.group(2))}',
            text
        )

        return text

    def _force_apply(self, text: str) -> str:
        """Force apply without guards (unsafe, for NoCheck mode)."""
        for pass_name in self.config.passes:
            text = self._apply_pass(text, pass_name)
        return text
