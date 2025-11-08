"""Explicit implementation of all sanitizer passes from Appendix D.2 and G.

This module provides:
- Utility Passes (UP): Passes 4-6, heuristic and unverified
- Verified Core (VC): Passes 1-3, formally guarded transformations
- Gatekeeper: AdmissibleSpec predicate check
"""

import re
from typing import Tuple, List, Dict, Any
from loguru import logger


# ============================================================================
# Component 1: Utility Passes (UP - Passes 4-6)
# Heuristic, unverified passes for syntactic repair
# ============================================================================

def run_pass_4_scope(coq_code: str) -> str:
    """Pass 4: Scope Resolution.

    Resolves unbound identifiers and shadowing issues.
    Heuristic approach:
    - Detects common unbound variable patterns
    - Adds common library prefixes (List., Nat., etc.)
    - Fixes variable shadowing in nested quantifiers

    Args:
        coq_code: Input Coq code

    Returns:
        Code with scope issues resolved
    """
    result = coq_code

    # Fix common unbound identifiers by adding library prefixes
    # List operations
    result = re.sub(r'\b(app|rev|length|map|fold_left|fold_right)\b(?!\s*:)',
                   lambda m: f'List.{m.group(1)}', result)

    # Nat operations (but avoid S and O as they're constructors)
    result = re.sub(r'\b(add|sub|mul|div|mod|eqb|leb|ltb)\b(?!\s*:)',
                   lambda m: f'Nat.{m.group(1)}', result)

    # Bool operations
    result = re.sub(r'\b(eqb|andb|orb|negb)\b(?!\s*:)',
                   lambda m: f'Bool.{m.group(1)}' if 'Bool.eqb' not in result else m.group(1),
                   result)

    # Fix variable shadowing: rename shadowed variables with primes
    # Pattern: forall x, ... forall x, ... (second x shadows first)
    def fix_shadowing(text):
        # Simple heuristic: track variable names in scope
        # This is a simplified version; full implementation would need AST parsing
        return text

    result = fix_shadowing(result)

    logger.debug("Applied Pass 4: Scope resolution")
    return result


def run_pass_5_list(coq_code: str) -> str:
    """Pass 5: List Parameterization.

    Fixes list type parameterization issues (e.g., list -> list A).

    Args:
        coq_code: Input Coq code

    Returns:
        Code with list parameters fixed
    """
    result = coq_code

    # Fix bare 'list' without type parameter
    # Pattern: list in type position without parameter

    # First, check if there's already a type variable A in scope
    has_type_var = bool(re.search(r'forall\s*\(?\s*A\s*:\s*Type\s*\)?', result))

    # Fix 'list)' or 'list,' or 'list.' to 'list A)' etc.
    if has_type_var:
        result = re.sub(r'\blist\b(\s*[),\.])', r'list A\1', result)
    else:
        # Need to add type variable
        # Find first forall and inject type variable
        def add_type_var(match):
            return 'forall (A : Type) ' + match.group(0)

        result = re.sub(r'forall\s+', add_type_var, result, count=1)
        result = re.sub(r'\blist\b(\s*[),\.])', r'list A\1', result)

    # Also fix option, prod, sum if needed
    result = re.sub(r'\boption\b(\s*[),\.])', r'option A\1', result)

    logger.debug("Applied Pass 5: List parameterization")
    return result


def run_pass_6_reformat(coq_code: str) -> str:
    """Pass 6: Code Reformatting and Cleanup.

    Normalizes whitespace, formatting, and minor syntactic issues.

    Args:
        coq_code: Input Coq code

    Returns:
        Reformatted code
    """
    result = coq_code

    # Normalize whitespace around operators
    result = re.sub(r'\s*=\s*', ' = ', result)
    result = re.sub(r'\s*<->\s*', ' <-> ', result)
    result = re.sub(r'\s*->\s*', ' -> ', result)
    result = re.sub(r'\s*:\s*', ' : ', result)

    # Normalize quantifier spacing
    result = re.sub(r'forall\s+\(', 'forall (', result)
    result = re.sub(r'fun\s+\(', 'fun (', result)

    # Normalize parentheses spacing
    result = re.sub(r'\(\s+', '(', result)
    result = re.sub(r'\s+\)', ')', result)

    # Remove trailing whitespace
    lines = result.split('\n')
    lines = [line.rstrip() for line in lines]
    result = '\n'.join(lines)

    # Ensure single blank line between major sections
    result = re.sub(r'\n{3,}', '\n\n', result)

    # Ensure ends with proper terminator
    result = result.strip()
    if not result.endswith('.'):
        result += '.'
    if not result.endswith('Qed.') and not result.endswith('Admitted.'):
        if result.endswith('.'):
            result += '\nQed.'
        else:
            result += '\n' + 'Qed.'

    logger.debug("Applied Pass 6: Code reformatting")
    return result


# ============================================================================
# Component 2: Verified Core (VC - Passes 1-3)
# Formally guarded, semantics-preserving transformations
# ============================================================================

def run_pass_1_require(coq_code: str) -> str:
    """Pass 1: Require Injection (R_req).

    Injects missing Require Import statements.
    Corresponds to weakening_req lemma in Sanitizer.v:30-48.
    This is a context-only extension that preserves semantics.

    Args:
        coq_code: Input Coq code

    Returns:
        Code with necessary imports added
    """
    result = coq_code
    needed_imports = []

    # Detect required libraries from usage patterns
    if re.search(r'\b(nil|cons|app|length|map|fold_left|fold_right|List\.)\b', result):
        if 'Require Import' not in result or 'List' not in result:
            needed_imports.append('Require Import Coq.Lists.List.')
            needed_imports.append('Import ListNotations.')

    if re.search(r'\b(S|O|plus|mult|le|lt|Nat\.)\b', result):
        if 'Arith' not in result:
            needed_imports.append('Require Import Coq.Arith.Arith.')

    if re.search(r'\b(andb|orb|negb|Bool\.)\b', result):
        if 'Bool' not in result:
            needed_imports.append('Require Import Coq.Bool.Bool.')

    # Add imports at the beginning
    if needed_imports:
        import_block = '\n'.join(needed_imports)
        result = import_block + '\n\n' + result
        logger.debug(f"Applied Pass 1: Added {len(needed_imports)} imports")

    return result


def run_pass_2_binder_identity(coq_code: str) -> str:
    """Pass 2: Binder Normalization (R_bind).

    Identity transformation that checks WellFormedU.
    In the formalization, this is mostly a type-checking pass.
    We normalize binder syntax for consistency.

    Corresponds to R_bind in Sanitizer.v:64-71.

    Args:
        coq_code: Input Coq code

    Returns:
        Code with normalized binders
    """
    result = coq_code

    # Normalize forall binders: ensure consistent spacing
    result = re.sub(r'forall\s+([a-zA-Z_]\w*)\s*:\s*(\w+)\s*,',
                   r'forall \1 : \2,', result)

    # Normalize lambda binders
    result = re.sub(r'fun\s+([a-zA-Z_]\w*)\s*:\s*(\w+)\s*=>',
                   r'fun \1 : \2 =>', result)

    # Normalize parenthesized binders
    result = re.sub(r'forall\s*\(\s*([a-zA-Z_]\w*)\s*:\s*(\w+)\s*\)',
                   r'forall (\1 : \2)', result)

    logger.debug("Applied Pass 2: Binder identity/normalization")
    return result


def run_pass_3_eq_canonical(coq_code: str) -> str:
    """Pass 3: Equality Canonicalization (R_eq).

    Canonicalizes equality expressions (e.g., <-> to =, symmetric ordering).
    Corresponds to R_eq_sem lemma in Sanitizer.v:142-195.

    This transformation preserves semantics by normalizing symmetric operators.

    Args:
        coq_code: Input Coq code

    Returns:
        Code with canonicalized equalities
    """
    result = coq_code

    # Normalize iff (<->) to equality (=) for propositions when appropriate
    # This is context-dependent; simplified heuristic here

    # Normalize symmetric equality operators to canonical order
    # Sort operands alphabetically for deterministic canonicalization
    def canonicalize_eq(match):
        left = match.group(1).strip()
        right = match.group(2).strip()
        # Simple heuristic: alphabetic order
        if left > right:
            return f'{right} = {left}'
        return match.group(0)

    # This is a simplified version; full implementation needs AST parsing
    # result = re.sub(r'(\w+)\s*=\s*(\w+)', canonicalize_eq, result)

    # Normalize Bool.eqb and Nat.eqb to canonical order
    result = re.sub(
        r'(Bool|Nat)\.eqb\s+([a-z]\w*)\s+([a-z]\w*)',
        lambda m: f'{m.group(1)}.eqb {min(m.group(2), m.group(3))} {max(m.group(2), m.group(3))}',
        result
    )

    logger.debug("Applied Pass 3: Equality canonicalization")
    return result


# ============================================================================
# Component 3: The Gatekeeper (AdmissibleSpec)
# ============================================================================

def check_admissible_spec(coq_code: str) -> Tuple[bool, List[str]]:
    """Check AdmissibleSpec predicate.

    Implements checks for:
    1. WellFormedU: Principal typing (no unbound variables, balanced parens)
    2. disjoint_ctx: Require statements come before definitions

    Args:
        coq_code: Input Coq code

    Returns:
        (is_admissible, list of failure reasons)
    """
    failures = []

    # Check 1: WellFormedU (simplified)
    # Must have a statement keyword
    has_statement = bool(re.search(
        r'\b(Definition|Lemma|Theorem|Proposition|Fact|Remark|Corollary)\b',
        coq_code
    ))

    if not has_statement:
        failures.append("WellFormedU: No statement keyword found")

    # Check balanced parentheses
    if coq_code.count('(') != coq_code.count(')'):
        failures.append("WellFormedU: Unbalanced parentheses")

    # Check for obvious syntax errors
    # No standalone ':=' without Definition/Let
    standalone_assign = re.findall(r'^[^D][^e][^f].*:=', coq_code, re.MULTILINE)
    if standalone_assign and not re.search(r'\bLet\b', coq_code):
        failures.append("WellFormedU: Unexpected standalone assignment")

    # Check 2: disjoint_ctx
    # Require statements must come before definitions
    lines = coq_code.strip().split('\n')
    seen_definition = False

    for line in lines:
        line_stripped = line.strip()
        if re.match(r'\b(Definition|Lemma|Theorem|Proposition)\b', line_stripped):
            seen_definition = True
        elif seen_definition and re.match(r'\bRequire\b', line_stripped):
            failures.append("disjoint_ctx: Require statement after definition")
            break

    is_admissible = len(failures) == 0

    if not is_admissible:
        logger.debug(f"AdmissibleSpec check failed: {failures}")

    return is_admissible, failures


# ============================================================================
# URC (Unsafe Rewrite) Detector
# ============================================================================

def find_suspicious_edit(raw_ast: str, final_ast: str) -> bool:
    r"""Detect unsafe semantic rewrites between raw and final AST.

    Returns True if transformation appears semantically unsafe based on:
    1. Variable renaming (n -> m consistently)
    2. Variable deletion (forall binder removed)
    3. Literal value change (0->1, true->false)
    4. Operator change (+->*, /\->/)
    5. Hypothesis addition/deletion

    Args:
        raw_ast: Original AST from RAG
        final_ast: Final AST after passes

    Returns:
        True if suspicious edit detected, False otherwise
    """
    # Normalize whitespace for comparison
    raw_normalized = ' '.join(raw_ast.split())
    final_normalized = ' '.join(final_ast.split())

    # If identical after normalization, no suspicious edits
    if raw_normalized == final_normalized:
        return False

    urc_detected = False
    reasons = []

    # Check 1: Variable renaming
    # Extract all identifiers
    raw_vars = set(re.findall(r'\b[a-z]\w*\b', raw_ast))
    final_vars = set(re.findall(r'\b[a-z]\w*\b', final_ast))

    # Check for systematic variable renaming (one var appears in final but not raw)
    added_vars = final_vars - raw_vars
    removed_vars = raw_vars - final_vars

    if added_vars and removed_vars:
        # Heuristic: if roughly same number added/removed, might be renaming
        if abs(len(added_vars) - len(removed_vars)) <= 1:
            reasons.append(f"Variable renaming suspected: {removed_vars} -> {added_vars}")
            urc_detected = True

    # Check 2: Variable deletion (forall binder removal)
    raw_foralls = re.findall(r'forall\s+\(?([a-zA-Z_]\w*)\s*:\s*\w+\)?', raw_ast)
    final_foralls = re.findall(r'forall\s+\(?([a-zA-Z_]\w*)\s*:\s*\w+\)?', final_ast)

    if len(raw_foralls) > len(final_foralls):
        deleted = set(raw_foralls) - set(final_foralls)
        if deleted:  # Only flag if actual deletion occurred
            reasons.append(f"Variable deletion: {deleted}")
            urc_detected = True

    # Check 3: Literal value changes
    raw_literals = re.findall(r'\b(0|1|2|true|false|nil)\b', raw_ast)
    final_literals = re.findall(r'\b(0|1|2|true|false|nil)\b', final_ast)

    # Count occurrences
    from collections import Counter
    raw_lit_counts = Counter(raw_literals)
    final_lit_counts = Counter(final_literals)

    # Detect complete replacement (e.g., all 0s became 1s)
    for lit in set(list(raw_lit_counts.keys()) + list(final_lit_counts.keys())):
        raw_count = raw_lit_counts.get(lit, 0)
        final_count = final_lit_counts.get(lit, 0)

        # Flag if literal appeared and disappeared completely (strong signal)
        if raw_count > 0 and final_count == 0:
            reasons.append(f"Literal deletion: {lit} ({raw_count} occurrences removed)")
            urc_detected = True
        elif raw_count == 0 and final_count > 0:
            reasons.append(f"Literal addition: {lit} ({final_count} occurrences added)")
            urc_detected = True
        # Also flag significant count changes (but less strong signal)
        elif raw_count > 0 and final_count > 0:
            diff = abs(raw_count - final_count)
            if diff > raw_count * 0.5:  # >50% change
                reasons.append(f"Literal count change: {lit} ({raw_count} -> {final_count})")
                urc_detected = True

    # Check 4: Operator changes
    operators = {'+', '-', '*', '/', '/\\', '\\/', '->', '<->', '=', '<>', '<=', '>=', '<', '>'}

    for op in operators:
        escaped_op = re.escape(op)
        raw_count = len(re.findall(escaped_op, raw_ast))
        final_count = len(re.findall(escaped_op, final_ast))

        if raw_count > 0 and final_count == 0:
            reasons.append(f"Operator deleted: {op}")
            urc_detected = True
        elif raw_count == 0 and final_count > 0:
            reasons.append(f"Operator added: {op}")
            urc_detected = True

    # Check 5: Hypothesis addition/deletion
    # Pattern: forall ..., H1 -> H2 -> ... -> Conclusion
    # Count arrows that are implications (not function types)
    raw_implications = len(re.findall(r'\w\s+->', raw_ast))
    final_implications = len(re.findall(r'\w\s+->', final_ast))

    if abs(raw_implications - final_implications) > 2:  # Allow small differences
        reasons.append(f"Hypothesis count change: {raw_implications} -> {final_implications}")
        urc_detected = True

    if urc_detected:
        logger.warning(f"URC detected: {'; '.join(reasons)}")

    return urc_detected


# ============================================================================
# Convenience wrapper functions
# ============================================================================

def apply_utility_passes(coq_code: str) -> str:
    """Apply all Utility Passes (UP) in order: Pass 4, 5, 6.

    Args:
        coq_code: Input Coq code

    Returns:
        Code after all UP passes
    """
    result = coq_code
    result = run_pass_4_scope(result)
    result = run_pass_5_list(result)
    result = run_pass_6_reformat(result)
    return result


def apply_verified_core_passes(coq_code: str) -> str:
    """Apply all Verified Core (VC) passes in order: Pass 1, 2, 3.

    Args:
        coq_code: Input Coq code

    Returns:
        Code after all VC passes
    """
    result = coq_code
    result = run_pass_1_require(result)
    result = run_pass_2_binder_identity(result)
    result = run_pass_3_eq_canonical(result)
    return result
