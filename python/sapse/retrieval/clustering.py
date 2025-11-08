"""Semantic clustering for proof steps and lemmas."""

from typing import List, Optional

import numpy as np
from loguru import logger


class SemanticClusterer:
    """
    Semantic clustering using KMeans or HDBSCAN.

    Example:
        >>> clusterer = SemanticClusterer(method="kmeans", n_clusters=10)
        >>> labels = clusterer.fit_predict(vectors)
        >>> print(f"Found {len(set(labels))} clusters")
    """

    def __init__(
        self,
        method: str = "kmeans",
        n_clusters: int = 10,
        min_cluster_size: int = 5,
        random_state: int = 42,
    ):
        """
        Initialize semantic clusterer.

        Args:
            method: Clustering method ('kmeans' or 'hdbscan').
            n_clusters: Number of clusters for KMeans.
            min_cluster_size: Minimum cluster size for HDBSCAN.
            random_state: Random seed for reproducibility.
        """
        self.method = method.lower()
        self.n_clusters = n_clusters
        self.min_cluster_size = min_cluster_size
        self.random_state = random_state
        self.model = None

        logger.info(f"Initialized SemanticClusterer with method={method}")

    def fit_predict(self, vectors: np.ndarray) -> np.ndarray:
        """
        Fit clustering model and predict labels.

        Args:
            vectors: numpy array of shape (n_samples, n_features).

        Returns:
            Cluster labels array of shape (n_samples,).

        Example:
            >>> labels = clusterer.fit_predict(embeddings)
            >>> unique_clusters = len(set(labels))
        """
        if self.method == "kmeans":
            return self._kmeans_clustering(vectors)
        elif self.method == "hdbscan":
            return self._hdbscan_clustering(vectors)
        else:
            raise ValueError(f"Unknown clustering method: {self.method}")

    def _kmeans_clustering(self, vectors: np.ndarray) -> np.ndarray:
        """Perform KMeans clustering."""
        try:
            from sklearn.cluster import KMeans
        except ImportError:
            logger.error("scikit-learn not installed. Run: pip install scikit-learn")
            raise

        self.model = KMeans(
            n_clusters=self.n_clusters,
            random_state=self.random_state,
            n_init=10,
        )
        labels = self.model.fit_predict(vectors)

        logger.info(f"KMeans clustering: {self.n_clusters} clusters from {len(vectors)} vectors")
        return labels

    def _hdbscan_clustering(self, vectors: np.ndarray) -> np.ndarray:
        """Perform HDBSCAN clustering."""
        try:
            import hdbscan
        except ImportError:
            logger.error("hdbscan not installed. Run: pip install hdbscan")
            raise

        self.model = hdbscan.HDBSCAN(
            min_cluster_size=self.min_cluster_size,
            metric="euclidean",
            cluster_selection_method="eom",
        )
        labels = self.model.fit_predict(vectors)

        n_clusters = len(set(labels)) - (1 if -1 in labels else 0)
        n_noise = list(labels).count(-1)
        logger.info(
            f"HDBSCAN clustering: {n_clusters} clusters, {n_noise} noise points from {len(vectors)} vectors"
        )
        return labels

    def get_cluster_centers(self) -> Optional[np.ndarray]:
        """
        Get cluster centers (only for KMeans).

        Returns:
            Cluster centers array of shape (n_clusters, n_features), or None.

        Example:
            >>> centers = clusterer.get_cluster_centers()
        """
        if self.method == "kmeans" and self.model is not None:
            return self.model.cluster_centers_
        return None

    def get_cluster_members(
        self, labels: np.ndarray, cluster_id: int
    ) -> np.ndarray:
        """
        Get indices of vectors belonging to a cluster.

        Args:
            labels: Cluster labels from fit_predict.
            cluster_id: Target cluster ID.

        Returns:
            Array of indices belonging to the cluster.

        Example:
            >>> members = clusterer.get_cluster_members(labels, cluster_id=0)
            >>> cluster_0_vectors = vectors[members]
        """
        return np.where(labels == cluster_id)[0]
