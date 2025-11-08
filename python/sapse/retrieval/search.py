"""Semantic search and retrieval evaluation."""

from typing import Dict, List, Tuple

import numpy as np
from loguru import logger

from .index import VectorIndex


class SemanticSearcher:
    """
    Semantic search engine with evaluation metrics.

    Example:
        >>> searcher = SemanticSearcher(index, embedder)
        >>> results = searcher.search_texts(["query text"], k=10)
        >>> for item in results[0]:
        ...     print(item["text"], item["score"])
    """

    def __init__(self, index: VectorIndex, embedder):
        """
        Initialize semantic searcher.

        Args:
            index: VectorIndex instance.
            embedder: TextEmbedder instance for encoding queries.
        """
        self.index = index
        self.embedder = embedder
        logger.info("Initialized SemanticSearcher")

    def search_texts(
        self, queries: List[str], k: int = 10, threshold: float = 0.0
    ) -> List[List[Dict]]:
        """
        Search for similar texts.

        Args:
            queries: List of query strings.
            k: Number of results to return per query.
            threshold: Minimum similarity threshold (0-1).

        Returns:
            List of result lists, where each result is a dict with
            'score', 'index', and metadata fields.

        Example:
            >>> results = searcher.search_texts(["forall a b, a + b = b + a"], k=5)
            >>> results[0][0]["text"]  # Top result text
        """
        # Embed queries
        query_vectors = self.embedder.embed_texts(queries)

        # Search index
        distances, indices, metadata_list = self.index.search(query_vectors, k)

        # Convert distances to similarity scores (cosine similarity approximation)
        # For L2 distance with normalized vectors: similarity ≈ 1 - (distance^2 / 2)
        # Here we use a simple conversion: score = 1 / (1 + distance)
        results = []
        for i, (dists, idxs, metas) in enumerate(
            zip(distances, indices, metadata_list)
        ):
            query_results = []
            for dist, idx, meta in zip(dists, idxs, metas):
                score = 1.0 / (1.0 + float(dist))

                if score >= threshold:
                    result = {
                        "score": score,
                        "index": int(idx),
                        **meta,
                    }
                    query_results.append(result)

            results.append(query_results)

        logger.debug(
            f"Searched {len(queries)} queries, returned {sum(len(r) for r in results)} total results"
        )
        return results

    def search_single(self, query: str, k: int = 10) -> List[Dict]:
        """
        Search for a single query.

        Args:
            query: Query string.
            k: Number of results.

        Returns:
            List of result dicts.

        Example:
            >>> results = searcher.search_single("Lemma about addition", k=3)
        """
        return self.search_texts([query], k=k)[0]


def compute_recall_at_k(
    retrieved: List[List[str]], relevant: List[List[str]], k: int = 10
) -> float:
    """
    Compute Recall@k metric.

    Args:
        retrieved: List of lists of retrieved item IDs.
        relevant: List of lists of relevant item IDs (ground truth).
        k: Cutoff for recall.

    Returns:
        Recall@k score (0-1).

    Example:
        >>> retrieved = [["L1", "L2", "L3"], ["L4", "L5"]]
        >>> relevant = [["L1", "L5"], ["L4"]]
        >>> recall = compute_recall_at_k(retrieved, relevant, k=5)
    """
    if not relevant:
        return 0.0

    recalls = []
    for retr, relv in zip(retrieved, relevant):
        if not relv:
            continue

        retr_at_k = set(retr[:k])
        relv_set = set(relv)

        recall = len(retr_at_k & relv_set) / len(relv_set)
        recalls.append(recall)

    return sum(recalls) / len(recalls) if recalls else 0.0


def compute_map_at_k(
    retrieved: List[List[str]], relevant: List[List[str]], k: int = 10
) -> float:
    """
    Compute Mean Average Precision at k (MAP@k).

    Args:
        retrieved: List of lists of retrieved item IDs.
        relevant: List of lists of relevant item IDs.
        k: Cutoff for MAP.

    Returns:
        MAP@k score (0-1).

    Example:
        >>> map_score = compute_map_at_k(retrieved, relevant, k=10)
    """
    if not relevant:
        return 0.0

    avg_precisions = []
    for retr, relv in zip(retrieved, relevant):
        if not relv:
            continue

        retr_at_k = retr[:k]
        relv_set = set(relv)

        precisions = []
        num_relevant_seen = 0

        for i, item in enumerate(retr_at_k, 1):
            if item in relv_set:
                num_relevant_seen += 1
                precision = num_relevant_seen / i
                precisions.append(precision)

        avg_precision = sum(precisions) / len(relv_set) if precisions else 0.0
        avg_precisions.append(avg_precision)

    return sum(avg_precisions) / len(avg_precisions) if avg_precisions else 0.0
