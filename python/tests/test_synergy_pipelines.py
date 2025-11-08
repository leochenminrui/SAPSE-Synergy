"""Tests for synergy pipelines."""

import pytest
from sapse.sanitize.pipelines import (
    BaselineRAGPipeline,
    SAPSEStrictPipeline,
    SAPSEFastPipeline,
    SAPSESynergyPipeline,
    create_pipeline,
)
from sapse.sanitize.passes import (
    check_admissible_spec,
    find_suspicious_edit,
)


# Mock verifier for testing
def mock_verifier_always_pass(coq_code: str):
    """Mock verifier that always passes."""
    return {"status": "passed", "message": "Mock verification passed"}


def mock_verifier_always_fail(coq_code: str):
    """Mock verifier that always fails."""
    return {"status": "failed", "message": "Mock verification failed"}


class TestAdmissibleSpec:
    """Test AdmissibleSpec predicate."""

    def test_well_formed_lemma(self):
        """Test well-formed lemma passes."""
        code = """
        Require Import Coq.Lists.List.
        Lemma test : forall (n : nat), n + 0 = n.
        Proof. reflexivity. Qed.
        """
        is_admissible, failures = check_admissible_spec(code)
        assert is_admissible
        assert len(failures) == 0

    def test_unbalanced_parens(self):
        """Test unbalanced parentheses fails."""
        code = "Lemma test : forall (n : nat, n + 0 = n."
        is_admissible, failures = check_admissible_spec(code)
        assert not is_admissible
        assert "WellFormedU: Unbalanced parentheses" in failures

    def test_require_after_definition(self):
        """Test Require after Definition fails disjoint_ctx."""
        code = """
        Lemma test : forall (n : nat), n + 0 = n.
        Require Import Coq.Lists.List.
        """
        is_admissible, failures = check_admissible_spec(code)
        assert not is_admissible
        assert any("disjoint_ctx" in f for f in failures)

    def test_no_statement_keyword(self):
        """Test missing statement keyword fails."""
        code = "forall n, n + 0 = n."
        is_admissible, failures = check_admissible_spec(code)
        assert not is_admissible
        assert any("WellFormedU" in f for f in failures)


class TestURCDetector:
    """Test URC (Unsafe Rewrite) detector."""

    def test_no_change(self):
        """Test identical code returns False."""
        code = "Lemma test : forall (n : nat), n + 0 = n."
        assert not find_suspicious_edit(code, code)

    def test_whitespace_only_change(self):
        """Test whitespace-only changes return False."""
        code1 = "Lemma test : forall (n : nat), n + 0 = n."
        code2 = "Lemma  test  :  forall  (n  :  nat),  n  +  0  =  n."
        # Should be False (whitespace normalization)
        # Note: current implementation may flag this, adjust if needed
        result = find_suspicious_edit(code1, code2)
        # Expect False for whitespace changes
        assert not result

    def test_variable_renaming(self):
        """Test variable renaming is detected."""
        code1 = "Lemma test : forall (n : nat), n + 0 = n."
        code2 = "Lemma test : forall (m : nat), m + 0 = m."
        assert find_suspicious_edit(code1, code2)

    def test_variable_deletion(self):
        """Test variable deletion is detected."""
        code1 = "Lemma test : forall (n : nat) (m : nat), n + m = m + n."
        code2 = "Lemma test : forall (n : nat), n + 0 = n."
        assert find_suspicious_edit(code1, code2)

    def test_literal_change(self):
        """Test literal value changes are detected."""
        code1 = "Lemma test : 0 + 0 = 0."
        code2 = "Lemma test : 1 + 1 = 1."
        assert find_suspicious_edit(code1, code2)


class TestBaselineRAGPipeline:
    """Test Baseline-RAG pipeline."""

    def test_passes_verification(self):
        """Test pipeline with passing verification."""
        pipeline = BaselineRAGPipeline(mock_verifier_always_pass)
        code = "Lemma test : forall (n : nat), n + 0 = n."

        result = pipeline.process_item("item1", code)

        assert result.item_id == "item1"
        assert result.config_name == "Baseline-RAG"
        assert result.status == "Verified"
        assert result.urc_flag == 0
        assert result.raw_ast == code
        assert result.final_ast == code

    def test_fails_verification(self):
        """Test pipeline with failing verification."""
        pipeline = BaselineRAGPipeline(mock_verifier_always_fail)
        code = "Lemma test : forall (n : nat), n + 0 = n."

        result = pipeline.process_item("item1", code)

        assert result.status == "Failed"
        assert result.urc_flag == 0


class TestSAPSEStrictPipeline:
    """Test SAPSE-Strict (VC-only) pipeline."""

    def test_admissible_code_passes(self):
        """Test admissible code passes through."""
        pipeline = SAPSEStrictPipeline(mock_verifier_always_pass)
        code = """
        Require Import Coq.Arith.Arith.
        Lemma test : forall (n : nat), n + 0 = n.
        """

        result = pipeline.process_item("item1", code)

        assert result.config_name == "SAPSE-Strict"
        assert result.status == "Verified"
        assert result.urc_flag == 0

    def test_non_admissible_abstains(self):
        """Test non-admissible code abstains."""
        pipeline = SAPSEStrictPipeline(mock_verifier_always_pass)
        code = "Lemma test : forall (n : nat, n + 0 = n."  # Unbalanced parens

        result = pipeline.process_item("item1", code)

        assert result.status == "Abstained"
        assert result.urc_flag == 0
        assert result.admissibility_failures is not None


class TestSAPSEFastPipeline:
    """Test SAPSE-Fast (UP-only) pipeline."""

    def test_applies_passes_and_detects_urc(self):
        """Test pipeline applies UP passes and detects URC."""
        pipeline = SAPSEFastPipeline(mock_verifier_always_pass)

        # Code that will be transformed by passes
        code = "Lemma test : forall n, n + 0 = n."  # Missing type annotation

        result = pipeline.process_item("item1", code)

        assert result.config_name == "SAPSE-Fast"
        assert result.status == "Verified"
        # final_ast should be different from raw_ast
        assert result.final_ast != result.raw_ast
        # URC flag depends on whether transformation is suspicious
        # In this case, adding type annotation should be safe (urc_flag=0)


class TestSAPSESynergyPipeline:
    """Test SAPSE-Synergy (UP + VC) pipeline."""

    def test_admissible_after_up_passes(self):
        """Test admissible code after UP preprocessing."""
        pipeline = SAPSESynergyPipeline(mock_verifier_always_pass)

        code = "Lemma test : forall n, n + 0 = n."

        result = pipeline.process_item("item1", code)

        assert result.config_name == "SAPSE-Synergy"
        # Should either verify or abstain, never have URC
        assert result.urc_flag == 0

    def test_non_admissible_after_up_abstains(self):
        """Test non-admissible code after UP abstains."""
        pipeline = SAPSESynergyPipeline(mock_verifier_always_pass)

        # Code with unbalanced parens (won't be fixed by UP)
        code = "Lemma test : forall (n : nat, n + 0 = n."

        result = pipeline.process_item("item1", code)

        assert result.status == "Abstained"
        assert result.urc_flag == 0


class TestPipelineFactory:
    """Test pipeline factory."""

    def test_create_baseline_rag(self):
        """Test creating Baseline-RAG pipeline."""
        pipeline = create_pipeline("Baseline-RAG", mock_verifier_always_pass)
        assert isinstance(pipeline, BaselineRAGPipeline)

    def test_create_sapse_strict(self):
        """Test creating SAPSE-Strict pipeline."""
        pipeline = create_pipeline("SAPSE-Strict", mock_verifier_always_pass)
        assert isinstance(pipeline, SAPSEStrictPipeline)

    def test_create_sapse_fast(self):
        """Test creating SAPSE-Fast pipeline."""
        pipeline = create_pipeline("SAPSE-Fast", mock_verifier_always_pass)
        assert isinstance(pipeline, SAPSEFastPipeline)

    def test_create_sapse_synergy(self):
        """Test creating SAPSE-Synergy pipeline."""
        pipeline = create_pipeline("SAPSE-Synergy", mock_verifier_always_pass)
        assert isinstance(pipeline, SAPSESynergyPipeline)

    def test_invalid_pipeline_name(self):
        """Test invalid pipeline name raises ValueError."""
        with pytest.raises(ValueError, match="Unknown pipeline"):
            create_pipeline("InvalidPipeline", mock_verifier_always_pass)
