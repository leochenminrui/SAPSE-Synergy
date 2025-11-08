"""Smoke tests for the full pipeline."""

import tempfile
from pathlib import Path

import pytest

from sapse.config import Config
from sapse.datasets import DatasetLoader


def test_config_loading():
    """Test configuration loading."""
    # Test with non-existent file (should use defaults)
    config = Config.from_yaml("nonexistent.yaml")
    assert config.get("embedder.type", "e5") == "e5"

    # Test set and get
    config.set("test.key", "value")
    assert config.get("test.key") == "value"


def test_dataset_loading():
    """Test dataset loading."""
    # Create temporary JSONL file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".jsonl", delete=False) as f:
        f.write('{"id": "1", "text": "test1"}\n')
        f.write('{"id": "2", "text": "test2"}\n')
        temp_file = f.name

    try:
        loader = DatasetLoader(temp_file)
        items = loader.load_all()

        assert len(items) == 2
        assert items[0]["id"] == "1"
        assert items[1]["text"] == "test2"

    finally:
        Path(temp_file).unlink()


def test_nl_proof_parser():
    """Test NL proof parsing."""
    from sapse.io_nl import NLProofParser

    parser = NLProofParser()
    proof = "Step 1: Use induction. Step 2: Apply lemma. Step 3: QED."

    steps = parser.extract_steps(proof)

    assert len(steps) == 3
    assert steps[0]["step_num"] == 1
    assert "induction" in steps[0]["text"]


def test_coq_lemma_parser():
    """Test Coq lemma parsing."""
    from sapse.io_coq import CoqLemmaParser

    parser = CoqLemmaParser()
    coq_text = "Lemma plus_comm: forall a b, a + b = b + a."

    lemma = parser.parse_lemma(coq_text)

    assert lemma is not None
    assert lemma["name"] == "plus_comm"
    assert "forall" in lemma["statement"]


def test_rag_template():
    """Test RAG template rendering."""
    from sapse.abstraction import PromptTemplate

    template = PromptTemplate("Hello {{NAME}}, you are {{AGE}} years old.")
    rendered = template.render({"NAME": "Alice", "AGE": "25"})

    assert rendered == "Hello Alice, you are 25 years old."


@pytest.mark.skip("Requires embedder models")
def test_full_pipeline_smoke():
    """Smoke test for full pipeline (requires models)."""
    from sapse.pipeline import SAPSEPipeline

    config = Config()
    config.set("embedder.type", "e5")
    config.set("verify.use_mock", True)

    pipeline = SAPSEPipeline(config)

    # This would require actual data and models
    # Skipping for CI
    assert pipeline is not None
