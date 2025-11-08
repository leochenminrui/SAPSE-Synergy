"""Tests for retrieval subsystem."""

import tempfile

import numpy as np
import pytest

from sapse.retrieval import (
    SemanticClusterer,
    VectorIndex,
    compute_map_at_k,
    compute_recall_at_k,
)


def test_vector_index():
    """Test FAISS vector index."""
    dimension = 128
    index = VectorIndex(dimension=dimension)

    # Add vectors
    vectors = np.random.rand(10, dimension).astype(np.float32)
    metadata = [{"id": i, "text": f"item_{i}"} for i in range(10)]

    index.add_vectors(vectors, metadata)
    assert index.size == 10

    # Search
    query = np.random.rand(1, dimension).astype(np.float32)
    distances, indices, meta_results = index.search(query, k=5)

    assert distances.shape == (1, 5)
    assert indices.shape == (1, 5)
    assert len(meta_results) == 1
    assert len(meta_results[0]) == 5


def test_vector_index_save_load():
    """Test index save and load."""
    dimension = 128
    index = VectorIndex(dimension=dimension)

    vectors = np.random.rand(10, dimension).astype(np.float32)
    metadata = [{"id": i} for i in range(10)]
    index.add_vectors(vectors, metadata)

    # Save
    with tempfile.TemporaryDirectory() as tmpdir:
        path = f"{tmpdir}/test_index"
        index.save(path)

        # Load
        loaded = VectorIndex.load(path)
        assert loaded.size == 10
        assert len(loaded.metadata) == 10


def test_recall_at_k():
    """Test Recall@k metric."""
    retrieved = [["L1", "L2", "L3"], ["L4", "L5", "L6"]]
    relevant = [["L1", "L3"], ["L4"]]

    recall = compute_recall_at_k(retrieved, relevant, k=3)
    assert 0 <= recall <= 1
    assert recall > 0  # Should find some relevant items


def test_map_at_k():
    """Test MAP@k metric."""
    retrieved = [["L1", "L2", "L3"], ["L4", "L5", "L6"]]
    relevant = [["L1", "L3"], ["L4"]]

    map_score = compute_map_at_k(retrieved, relevant, k=3)
    assert 0 <= map_score <= 1


def test_semantic_clusterer():
    """Test semantic clustering."""
    vectors = np.random.rand(50, 128).astype(np.float32)

    # KMeans
    clusterer = SemanticClusterer(method="kmeans", n_clusters=5)
    labels = clusterer.fit_predict(vectors)

    assert len(labels) == 50
    assert len(set(labels)) <= 5  # At most 5 clusters

    # Get cluster centers
    centers = clusterer.get_cluster_centers()
    assert centers.shape == (5, 128)

    # Get members
    members = clusterer.get_cluster_members(labels, cluster_id=0)
    assert len(members) > 0
