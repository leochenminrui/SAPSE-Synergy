"""Tests for mock verifier."""

from sapse.verify import MockVerifier, PipelineMetrics


def test_mock_verifier():
    """Test mock verifier."""
    verifier = MockVerifier(pass_rate=0.8, random_seed=42)

    # Well-formed lemma
    coq_code = "Lemma test: True. Proof. trivial. Qed."
    result = verifier.verify(coq_code)

    assert result["status"] in ["passed", "failed", "fixable"]
    assert "message" in result
    assert "stdout" in result
    assert "stderr" in result


def test_mock_verifier_batch():
    """Test batch verification."""
    verifier = MockVerifier(pass_rate=0.7, random_seed=42)

    codes = [
        "Lemma t1: True. Proof. trivial. Qed.",
        "Lemma t2: False.",  # No proof
        "Lemma t3: forall n, n = n. Proof. reflexivity. Qed.",
    ]

    results = verifier.batch_verify(codes)
    assert len(results) == 3
    assert all("status" in r for r in results)


def test_pipeline_metrics():
    """Test pipeline metrics tracking."""
    metrics = PipelineMetrics()

    # Add verification results
    metrics.add_verification_result("passed")
    metrics.add_verification_result("passed")
    metrics.add_verification_result("failed")
    metrics.add_verification_result("fixable")

    # Add retrieval metrics
    metrics.add_retrieval_metrics(0.85, 0.75)
    metrics.add_retrieval_metrics(0.90, 0.80)

    # Compute summary
    summary = metrics.compute_summary()

    assert summary["conversion_rate"] == 0.5  # 2 passed out of 4
    assert summary["lemma_yield"] == 2
    assert summary["total_attempts"] == 4
    assert "recall_at_k" in summary
    assert "map_at_k" in summary


def test_metrics_print_summary():
    """Test metrics summary printing."""
    metrics = PipelineMetrics()

    metrics.add_verification_result("passed")
    metrics.add_verification_result("failed")

    # Should not raise
    metrics.print_summary()

    # Test save_to_dict
    data = metrics.save_to_dict()
    assert "raw_data" in data
    assert "summary" in data
