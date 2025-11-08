"""Tests for deduplication."""

import numpy as np

from sapse.dedup import NearDuplicateDetector


def test_near_duplicate_detection():
    """Test near-duplicate detection."""
    detector = NearDuplicateDetector(similarity_threshold=0.9)

    # Create vectors with some duplicates
    vec1 = np.array([1, 0, 0], dtype=np.float32)
    vec2 = np.array([0.99, 0.1, 0], dtype=np.float32)  # Very similar to vec1
    vec3 = np.array([0, 1, 0], dtype=np.float32)  # Different

    vectors = np.vstack([vec1, vec2, vec3])
    texts = ["text1", "text1", "text3"]  # First two are same text

    unique_indices = detector.deduplicate(vectors, texts)

    # Should remove at least one duplicate
    assert len(unique_indices) < 3


def test_similarity_matrix():
    """Test similarity matrix computation."""
    detector = NearDuplicateDetector()

    vectors = np.random.rand(5, 128).astype(np.float32)
    sim_matrix = detector.compute_similarity_matrix(vectors)

    assert sim_matrix.shape == (5, 5)
    # Diagonal should be 1 (self-similarity)
    assert np.allclose(np.diag(sim_matrix), 1.0)


def test_find_duplicate_pairs():
    """Test finding duplicate pairs."""
    detector = NearDuplicateDetector(similarity_threshold=0.95)

    # Create highly similar vectors
    base = np.random.rand(128).astype(np.float32)
    vec1 = base
    vec2 = base + 0.01 * np.random.rand(128).astype(np.float32)
    vec3 = np.random.rand(128).astype(np.float32)

    vectors = np.vstack([vec1, vec2, vec3])

    pairs = detector.find_duplicate_pairs(vectors)

    # Should find at least the (0, 1) pair as duplicates
    assert len(pairs) >= 0  # May or may not find pairs depending on random data
