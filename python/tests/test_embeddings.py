"""Tests for embedding backends."""

import numpy as np
import pytest

from sapse.embeddings import E5Embedder, TextEmbedder


class DummyEmbedder(TextEmbedder):
    """Dummy embedder for testing."""

    def __init__(self):
        super().__init__()
        self._dim = 128

    def embed_texts(self, texts):
        return np.random.rand(len(texts), self._dim).astype(np.float32)

    @property
    def embedding_dim(self):
        return self._dim


def test_text_embedder_interface():
    """Test base embedder interface."""
    embedder = DummyEmbedder()

    # Test single embedding
    vector = embedder.embed_single("hello")
    assert vector.shape == (128,)

    # Test batch embedding
    texts = ["hello", "world", "test"]
    vectors = embedder.embed_texts(texts)
    assert vectors.shape == (3, 128)

    # Test batch_embed
    vectors = embedder.batch_embed(texts, batch_size=2)
    assert vectors.shape == (3, 128)


def test_e5_embedder():
    """Test E5 embedder (requires model download)."""
    pytest.skip("Skipping E5 test - requires model download")

    embedder = E5Embedder()
    texts = ["query: test", "passage: hello world"]
    vectors = embedder.embed_texts(texts)

    assert vectors.shape[0] == 2
    assert vectors.shape[1] == embedder.embedding_dim


def test_embedder_caching():
    """Test embedder caching directory creation."""
    embedder = DummyEmbedder()
    assert embedder.cache_dir.exists()
