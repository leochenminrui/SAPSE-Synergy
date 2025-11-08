"""Post-generation Coq code sanitizer.

Light rule engine to fix common type annotation issues before coqc verification.
"""

import re
from typing import Set

ARITH_TOKENS: Set[str] = {"plus", "add", "+", "mult", "*", "le", "lt", "ge", "gt", "Nat", "S", "O"}


def _has_explicit_type_forall(src: str) -> bool:
    """Check if forall has explicit type annotations like 'forall (x : T)'."""
    return bool(re.search(r"forall\s*\([^:]+:\s*[^)]+\)", src))


def _inject_polymorphic_fallback(src: str) -> str:
    """Replace bare 'forall x,' with 'forall (A : Type) (x : A),'.

    Conservative: only when no explicit types are present.

    Args:
        src: Original Coq source code.

    Returns:
        Modified source with polymorphic types injected.

    Example:
        >>> _inject_polymorphic_fallback("forall x, x = x.")
        'forall (A : Type) (x : A), x = x.'
    """
    if not _has_explicit_type_forall(src):
        # Match 'forall x,' and replace with 'forall (A : Type) (x : A),'
        src = re.sub(
            r"forall\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*,",
            r"forall (A : Type) (\1 : A),",
            src
        )
    return src


def _prefer_nat_when_arith(src: str) -> str:
    """If arithmetic tokens present and no explicit types, default to nat.

    Args:
        src: Original Coq source code.

    Returns:
        Modified source with nat types for arithmetic contexts.

    Example:
        >>> _prefer_nat_when_arith("forall x, x + 0 = x.")
        'Require Import Coq.Arith.Arith.\\nforall (x : nat), x + 0 = x.'
    """
    if any(tok in src for tok in ARITH_TOKENS) and not _has_explicit_type_forall(src):
        # Replace 'forall x,' with 'forall (x : nat),'
        src = re.sub(
            r"forall\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*,",
            r"forall (\1 : nat),",
            src
        )
        # Ensure Nat imported
        if "Require Import Coq.Arith.Arith." not in src:
            src = "Require Import Coq.Arith.Arith.\n" + src
    return src


def sanitize_coq(src: str) -> str:
    """Apply sanitization rules to Coq source code.

    Applies:
    1. Polymorphic fallback for untyped forall
    2. Nat injection for arithmetic contexts
    3. Ensures proper Qed. termination

    Args:
        src: Original Coq source code (possibly incomplete).

    Returns:
        Sanitized Coq code ready for verification.

    Example:
        >>> sanitize_coq("Lemma test: forall x, x = x. Proof. reflexivity.")
        'Lemma test: forall (A : Type) (x : A), x = x. Proof. reflexivity.\\nQed.'
    """
    s = src.strip()

    # Apply type injection rules
    s = _inject_polymorphic_fallback(s)
    s = _prefer_nat_when_arith(s)

    # Normalize trailing periods, ensure Qed.
    if not s.strip().endswith("Qed."):
        if not s.strip().endswith("."):
            s += "."
        s += "\nQed."

    return s
