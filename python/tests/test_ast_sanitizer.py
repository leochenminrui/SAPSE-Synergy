"""Unit tests for AST-based sanitizer."""

import pytest
from sapse.verify.ast_sanitizer import ASTSanitizer, sanitize_with_ast


class TestASTSanitizer:
    """Test cases for AST sanitizer."""

    def test_add_missing_nat_imports(self):
        """Test that arithmetic imports are added for nat operations."""
        sanitizer = ASTSanitizer()
        code = "Lemma test : forall n, n + 0 = n."
        fixed, changed, fixes = sanitizer.sanitize(code)

        assert changed
        assert "Require Import Coq.Arith.Arith" in fixed or "Require Import Coq.Init.Nat" in fixed
        assert "forall (n : nat)" in fixed

    def test_fill_missing_types_nat(self):
        """Test type inference for nat variables."""
        sanitizer = ASTSanitizer()
        code = "Lemma plus_comm : forall n m, n + m = m + n."
        fixed, changed, fixes = sanitizer.sanitize(code)

        assert changed
        assert "nat" in fixed

    def test_fill_missing_types_polymorphic(self):
        """Test polymorphic type fallback."""
        sanitizer = ASTSanitizer()
        code = "Lemma refl : forall x, x = x."
        fixed, changed, fixes = sanitizer.sanitize(code)

        # Should add polymorphic type
        assert "Type" in fixed or "forall (x" in fixed

    def test_list_operations_import(self):
        """Test that list imports are added."""
        sanitizer = ASTSanitizer()
        code = "Lemma test : forall l, length l = 0."
        fixed, changed, fixes = sanitizer.sanitize(code)

        assert "Require Import Coq.Lists.List" in fixed

    def test_ensure_qed(self):
        """Test that Qed. is added if missing."""
        sanitizer = ASTSanitizer()
        code = "Lemma test : True. Proof. trivial"
        fixed, changed, fixes = sanitizer.sanitize(code)

        assert fixed.strip().endswith("Qed.")

    def test_multiple_passes(self):
        """Test that multiple passes can be applied."""
        config = {
            'fixes': ['add_missing_requires', 'fill_missing_types', 'normalize_binders'],
            'max_passes': 3
        }
        sanitizer = ASTSanitizer(max_passes=3)
        code = "Lemma test:forall n,n+0=n."
        fixed, changed, fixes = sanitizer.sanitize(code, config)

        assert changed
        # Should have better spacing and types
        assert "forall (" in fixed
        assert "nat" in fixed

    def test_convenience_function(self):
        """Test the convenience function."""
        code = "Lemma test : forall n, n = n."
        fixed, changed, fixes = sanitize_with_ast(code)

        assert isinstance(fixed, str)
        assert isinstance(changed, bool)
        assert isinstance(fixes, list)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
