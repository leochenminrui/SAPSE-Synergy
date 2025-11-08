"""Near-duplicate detection for lemmas."""

import re
from typing import List, Set

import numpy as np
from loguru import logger


class NearDuplicateDetector:
    """
    Detects and removes near-duplicate lemmas.

    Uses cosine similarity and normalized text comparison.

    Example:
        >>> detector = NearDuplicateDetector(threshold=0.9)
        >>> unique_indices = detector.deduplicate(vectors, texts)
        >>> unique_lemmas = [lemmas[i] for i in unique_indices]
    """

    def __init__(
        self,
        similarity_threshold: float = 0.9,
        use_text_normalization: bool = True,
    ):
        """
        Initialize near-duplicate detector.

        Args:
            similarity_threshold: Cosine similarity threshold (0-1).
            use_text_normalization: Whether to also check normalized text.
        """
        self.similarity_threshold = similarity_threshold
        self.use_text_normalization = use_text_normalization

        logger.info(
            f"Initialized NearDuplicateDetector with threshold={similarity_threshold}"
        )

    def deduplicate(
        self,
        vectors: np.ndarray,
        texts: List[str] = None,
    ) -> List[int]:
        """
        Find unique items, removing near-duplicates.

        Args:
            vectors: Embedding vectors of shape (n_items, dim).
            texts: Optional text strings for text-based deduplication.

        Returns:
            List of indices of unique items.

        Example:
            >>> unique_idx = detector.deduplicate(embeddings, lemma_texts)
            >>> unique_items = [items[i] for i in unique_idx]
        """
        n_items = len(vectors)
        is_unique = [True] * n_items
        seen_normalized: Set[str] = set()

        # Normalize vectors
        norms = np.linalg.norm(vectors, axis=1, keepdims=True)
        norms[norms == 0] = 1  # Avoid division by zero
        normalized_vectors = vectors / norms

        for i in range(n_items):
            if not is_unique[i]:
                continue

            # Check normalized text if available
            if self.use_text_normalization and texts:
                normalized_text = self._normalize_text(texts[i])
                if normalized_text in seen_normalized:
                    is_unique[i] = False
                    continue
                seen_normalized.add(normalized_text)

            # Check vector similarity with subsequent items
            for j in range(i + 1, n_items):
                if not is_unique[j]:
                    continue

                similarity = np.dot(normalized_vectors[i], normalized_vectors[j])

                if similarity >= self.similarity_threshold:
                    is_unique[j] = False
                    logger.debug(
                        f"Marked item {j} as duplicate of {i} (similarity={similarity:.3f})"
                    )

        unique_indices = [i for i in range(n_items) if is_unique[i]]

        logger.info(
            f"Deduplication: {len(unique_indices)} unique items from {n_items} total "
            f"({n_items - len(unique_indices)} duplicates removed)"
        )
        return unique_indices

    def _normalize_text(self, text: str) -> str:
        """
        Normalize text for comparison.

        Args:
            text: Input text.

        Returns:
            Normalized text (lowercase, no whitespace/punctuation).

        Example:
            >>> detector._normalize_text("Lemma  foo : True.")
            'lemmafootrue'
        """
        # Convert to lowercase
        text = text.lower()

        # Remove whitespace
        text = re.sub(r"\s+", "", text)

        # Remove common punctuation
        text = re.sub(r"[.,;:!?(){}[\]]", "", text)

        return text

    def compute_similarity_matrix(self, vectors: np.ndarray) -> np.ndarray:
        """
        Compute pairwise cosine similarity matrix.

        Args:
            vectors: Embedding vectors of shape (n_items, dim).

        Returns:
            Similarity matrix of shape (n_items, n_items).

        Example:
            >>> sim_matrix = detector.compute_similarity_matrix(vectors)
            >>> print(sim_matrix[0, 1])  # Similarity between item 0 and 1
        """
        # Normalize vectors
        norms = np.linalg.norm(vectors, axis=1, keepdims=True)
        norms[norms == 0] = 1
        normalized = vectors / norms

        # Compute cosine similarity
        similarity_matrix = np.dot(normalized, normalized.T)

        return similarity_matrix

    def find_duplicate_pairs(
        self, vectors: np.ndarray, texts: List[str] = None
    ) -> List[tuple]:
        """
        Find all duplicate pairs above threshold.

        Args:
            vectors: Embedding vectors.
            texts: Optional texts for labeling.

        Returns:
            List of (index1, index2, similarity) tuples.

        Example:
            >>> pairs = detector.find_duplicate_pairs(vectors)
            >>> for i, j, sim in pairs:
            ...     print(f"Items {i} and {j} are {sim:.2%} similar")
        """
        sim_matrix = self.compute_similarity_matrix(vectors)
        n_items = len(vectors)

        duplicate_pairs = []
        for i in range(n_items):
            for j in range(i + 1, n_items):
                if sim_matrix[i, j] >= self.similarity_threshold:
                    duplicate_pairs.append((i, j, sim_matrix[i, j]))

        logger.info(f"Found {len(duplicate_pairs)} duplicate pairs")
        return duplicate_pairs
