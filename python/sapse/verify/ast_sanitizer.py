"""Enhanced AST-based Coq sanitizer for structural fixes.

This module provides advanced sanitization using lightweight AST parsing
to fix common type annotation, scoping, and import issues before Coq verification.

Based on pilot ablation results showing ~65% "fixable" rate (Nov 2, 2025).
"""

import re
from typing import Dict, List, Set, Tuple
from loguru import logger


# Common Coq library imports for different domains
DOMAIN_IMPORTS = {
    "arith": ["Coq.Arith.Arith", "Coq.Init.Nat"],
    "zarith": ["Coq.ZArith.ZArith"],
    "list": ["Coq.Lists.List"],
    "bool": ["Coq.Bool.Bool"],
    "logic": ["Coq.Logic.Classical"],
    "reals": ["Coq.Reals.Reals"],
}

# Operator to type domain mapping
OPERATOR_DOMAINS = {
    "+": {"nat", "Z", "R"},
    "-": {"nat", "Z", "R"},
    "*": {"nat", "Z", "R"},
    "<=": {"nat", "Z", "R"},
    "<": {"nat", "Z", "R"},
    ">=": {"nat", "Z", "R"},
    ">": {"nat", "Z", "R"},
    "S": {"nat"},
    "O": {"nat"},
    "::": {"list"},
    "cons": {"list"},
    "nil": {"list"},
    "length": {"list"},
    "map": {"list"},
    "fold_left": {"list"},
    "fold_right": {"list"},
    "andb": {"bool"},
    "orb": {"bool"},
    "negb": {"bool"},
    "true": {"bool"},
    "false": {"bool"},
}

# Type inference heuristics
TYPE_KEYWORDS = {
    "nat": ["S", "O", "plus", "mult", "le", "lt"],
    "bool": ["true", "false", "andb", "orb", "negb"],
    "list": ["nil", "cons", "::", "length", "map", "fold"],
    "Z": ["Zplus", "Zmult", "Zle", "Zlt"],
}


class CoqToken:
    """Lightweight token for Coq parsing."""
    def __init__(self, type: str, value: str, pos: int):
        self.type = type  # 'keyword', 'ident', 'op', 'punct', 'type'
        self.value = value
        self.pos = pos

    def __repr__(self):
        return f"Token({self.type}, {self.value!r})"


class SymbolTable:
    """Tracks variables and their types in scope."""
    def __init__(self):
        self.bindings: Dict[str, str] = {}  # var_name -> type
        self.imports: Set[str] = set()

    def bind(self, var: str, typ: str):
        """Add variable binding."""
        self.bindings[var] = typ

    def lookup(self, var: str) -> str:
        """Get type of variable, or empty if unknown."""
        return self.bindings.get(var, "")

    def add_import(self, module: str):
        """Register an import."""
        self.imports.add(module)


class ASTSanitizer:
    """Enhanced AST-based Coq sanitizer.

    Applies multiple passes to fix structural issues:
    1. add_missing_requires - Insert missing Require Import statements
    2. fill_missing_types - Infer and fill missing type annotations
    3. normalize_binders - Canonicalize quantifier forms
    4. canon_equalities - Normalize equality expressions
    5. implicit_args - Handle implicit arguments properly

    Example:
        >>> sanitizer = ASTSanitizer()
        >>> code = "Lemma test : forall n, n + 0 = n."
        >>> fixed, changed = sanitizer.sanitize(code)
        >>> "nat" in fixed
        True
    """

    def __init__(self, max_passes: int = 3):
        """Initialize sanitizer.

        Args:
            max_passes: Maximum number of sanitization passes.
        """
        self.max_passes = max_passes
        self.symbol_table = SymbolTable()

    def tokenize(self, src: str) -> List[CoqToken]:
        """Lightweight tokenization of Coq code.

        Args:
            src: Coq source code.

        Returns:
            List of tokens.
        """
        # Simple regex-based tokenizer
        pattern = r'''
            (?P<keyword>forall|fun|Lemma|Theorem|Definition|Proof|Qed|Require|Import) |
            (?P<type>nat|bool|list|Z|R|Type|Prop|Set) |
            (?P<op>[+\-*/<>=:]+) |
            (?P<punct>[\(\)\[\]\{\},.;]) |
            (?P<ident>[a-zA-Z_][a-zA-Z0-9_]*) |
            (?P<ws>\s+)
        '''

        tokens = []
        pos = 0
        for match in re.finditer(pattern, src, re.VERBOSE):
            for name, value in match.groupdict().items():
                if value and name != 'ws':
                    tokens.append(CoqToken(name, value, pos))
                    pos += len(value)
        return tokens

    def infer_type_from_context(self, var: str, src: str) -> str:
        """Infer variable type from usage context.

        Args:
            var: Variable name.
            src: Source code containing usage.

        Returns:
            Inferred type ('nat', 'bool', 'list', etc.) or empty string.
        """
        # Check for type keywords in context
        for typ, keywords in TYPE_KEYWORDS.items():
            if any(kw in src for kw in keywords):
                return typ

        # Check for operators
        for op, domains in OPERATOR_DOMAINS.items():
            if op in src:
                # Prefer nat for arithmetic
                if "nat" in domains:
                    return "nat"
                return list(domains)[0]

        # Default polymorphic
        return ""

    def add_missing_requires(self, src: str) -> Tuple[str, bool]:
        """Add missing Require Import statements.

        Args:
            src: Coq source code.

        Returns:
            (modified_code, changed_flag)
        """
        changed = False
        needed_imports = set()

        # Detect which domains are used
        for op, domains in OPERATOR_DOMAINS.items():
            if re.search(rf'\b{re.escape(op)}\b', src):
                if "nat" in domains and any(kw in src for kw in ["S", "O", "+", "*"]):
                    needed_imports.update(DOMAIN_IMPORTS.get("arith", []))
                if "list" in domains:
                    needed_imports.update(DOMAIN_IMPORTS.get("list", []))
                if "bool" in domains:
                    needed_imports.update(DOMAIN_IMPORTS.get("bool", []))

        # Check for explicit type mentions
        if re.search(r'\blist\b', src):
            needed_imports.update(DOMAIN_IMPORTS.get("list", []))
        if re.search(r'\b(nat|S|O)\b', src):
            needed_imports.update(DOMAIN_IMPORTS.get("arith", []))
        if re.search(r'\b(bool|true|false)\b', src):
            needed_imports.update(DOMAIN_IMPORTS.get("bool", []))

        # Add imports that aren't already present
        imports_to_add = []
        for imp in needed_imports:
            if f"Require Import {imp}" not in src:
                imports_to_add.append(f"Require Import {imp}.")
                changed = True

        if imports_to_add:
            # Add at beginning
            import_block = "\n".join(imports_to_add)
            src = import_block + "\n\n" + src

        return src, changed

    def fill_missing_types(self, src: str) -> Tuple[str, bool]:
        """Fill missing type annotations in quantifiers.

        Args:
            src: Coq source code.

        Returns:
            (modified_code, changed_flag)
        """
        changed = False

        # Match 'forall x,' without type annotation
        pattern = r'forall\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*,'

        def replacer(match):
            nonlocal changed
            var = match.group(1)

            # Skip if already has type annotation
            before = src[:match.start()]
            after = src[match.end():]

            # Check if this is part of a typed binding like 'forall (x : T),'
            if re.search(rf'forall\s*\(\s*{var}\s*:\s*\w+\s*\)', before + match.group(0)):
                return match.group(0)

            # Infer type
            typ = self.infer_type_from_context(var, src)

            if not typ:
                # Default to polymorphic
                typ = "A"
                # Add Type binding if not present
                if "forall (A : Type)" not in src:
                    changed = True
                    return f"forall (A : Type) ({var} : A),"

            changed = True
            return f"forall ({var} : {typ}),"

        result = re.sub(pattern, replacer, src)
        return result, changed

    def normalize_binders(self, src: str) -> Tuple[str, bool]:
        """Normalize quantifier binder syntax.

        Args:
            src: Coq source code.

        Returns:
            (modified_code, changed_flag)
        """
        changed = False

        # Ensure consistent spacing in forall
        old_src = src
        src = re.sub(r'forall\s+\(\s*', 'forall (', src)
        src = re.sub(r'\s*:\s*', ' : ', src)
        src = re.sub(r'\s*\),', '),', src)

        changed = (src != old_src)
        return src, changed

    def canon_equalities(self, src: str) -> Tuple[str, bool]:
        """Canonicalize equality expressions.

        Args:
            src: Coq source code.

        Returns:
            (modified_code, changed_flag)
        """
        # This is a placeholder - actual implementation would need
        # more sophisticated AST analysis
        return src, False

    def handle_implicit_args(self, src: str) -> Tuple[str, bool]:
        """Handle implicit arguments properly.

        Args:
            src: Coq source code.

        Returns:
            (modified_code, changed_flag)
        """
        changed = False

        # Add {A} for polymorphic lemmas if needed
        if "forall (A : Type)" in src:
            # Check if using list or other polymorphic types
            if re.search(r'list\s+A', src):
                # Ensure Import ListNotations
                if "Import ListNotations" not in src and "Require Import Coq.Lists.List" in src:
                    src = src.replace(
                        "Require Import Coq.Lists.List.",
                        "Require Import Coq.Lists.List. Import ListNotations."
                    )
                    changed = True

        return src, changed

    def ensure_qed(self, src: str) -> str:
        """Ensure lemma ends with Qed.

        Args:
            src: Coq source code.

        Returns:
            Modified code ending with Qed.
        """
        src = src.strip()
        if not src.endswith("Qed."):
            if not src.endswith("."):
                src += "."
            src += "\nQed."
        return src

    def sanitize(self, coq_code: str, config: Dict = None) -> Tuple[str, bool, List[str]]:
        """Apply all sanitization passes.

        Args:
            coq_code: Original Coq code.
            config: Optional configuration dict with 'fixes' list.

        Returns:
            (sanitized_code, was_changed, applied_fixes)
        """
        config = config or {}
        fixes_to_apply = config.get('fixes', [
            'add_missing_requires',
            'fill_missing_types',
            'normalize_binders',
            'canon_equalities',
            'implicit_args'
        ])

        src = coq_code
        overall_changed = False
        applied = []

        for pass_num in range(self.max_passes):
            pass_changed = False

            if 'add_missing_requires' in fixes_to_apply:
                src, changed = self.add_missing_requires(src)
                if changed:
                    applied.append(f"pass{pass_num+1}:add_requires")
                    pass_changed = True

            if 'fill_missing_types' in fixes_to_apply:
                src, changed = self.fill_missing_types(src)
                if changed:
                    applied.append(f"pass{pass_num+1}:fill_types")
                    pass_changed = True

            if 'normalize_binders' in fixes_to_apply:
                src, changed = self.normalize_binders(src)
                if changed:
                    applied.append(f"pass{pass_num+1}:normalize")
                    pass_changed = True

            if 'canon_equalities' in fixes_to_apply:
                src, changed = self.canon_equalities(src)
                if changed:
                    applied.append(f"pass{pass_num+1}:canon_eq")
                    pass_changed = True

            if 'implicit_args' in fixes_to_apply:
                src, changed = self.handle_implicit_args(src)
                if changed:
                    applied.append(f"pass{pass_num+1}:implicit")
                    pass_changed = True

            overall_changed = overall_changed or pass_changed

            # Stop if no changes in this pass
            if not pass_changed:
                break

        # Always ensure Qed
        src = self.ensure_qed(src)

        if applied:
            logger.debug(f"AST sanitizer applied: {', '.join(applied)}")

        return src, overall_changed, applied


def sanitize_with_ast(coq_code: str, config: Dict = None) -> Tuple[str, bool, List[str]]:
    """Convenience function for AST sanitization.

    Args:
        coq_code: Original Coq code.
        config: Optional configuration dict.

    Returns:
        (sanitized_code, was_changed, applied_fixes)

    Example:
        >>> code = "Lemma test : forall n, n + 0 = n."
        >>> fixed, changed, fixes = sanitize_with_ast(code)
        >>> changed
        True
    """
    sanitizer = ASTSanitizer(max_passes=config.get('max_passes', 3) if config else 3)
    return sanitizer.sanitize(coq_code, config)
