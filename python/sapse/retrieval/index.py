"""FAISS index management for vector retrieval."""

import pickle
from pathlib import Path
from typing import Any, Dict, List, Optional

import numpy as np
from loguru import logger


class VectorIndex:
    """
    Vector index for similarity search using FAISS.

    Manages FAISS indices and associated metadata.

    Example:
        >>> index = VectorIndex(dimension=768)
        >>> index.add_vectors(vectors, metadata)
        >>> index.save("data/index/lemmas.faiss")
        >>> loaded = VectorIndex.load("data/index/lemmas.faiss")
    """

    def __init__(self, dimension: int, use_gpu: bool = False):
        """
        Initialize vector index.

        Args:
            dimension: Embedding dimension.
            use_gpu: Whether to use GPU acceleration (requires faiss-gpu).
        """
        self.dimension = dimension
        self.use_gpu = use_gpu
        self.metadata: List[Dict[str, Any]] = []

        try:
            import faiss

            self.faiss = faiss
        except ImportError:
            logger.error("faiss not installed. Run: pip install faiss-cpu")
            raise

        # Create flat L2 index (can be extended to IVF, HNSW, etc.)
        self.index = faiss.IndexFlatL2(dimension)

        if use_gpu and faiss.get_num_gpus() > 0:
            logger.info("Using GPU acceleration for FAISS")
            self.index = faiss.index_cpu_to_gpu(
                faiss.StandardGpuResources(), 0, self.index
            )
        else:
            logger.info("Using CPU for FAISS index")

        logger.info(f"Initialized FAISS index with dimension={dimension}")

    def add_vectors(
        self, vectors: np.ndarray, metadata: Optional[List[Dict[str, Any]]] = None
    ):
        """
        Add vectors to the index.

        Args:
            vectors: numpy array of shape (n_vectors, dimension).
            metadata: Optional list of metadata dicts for each vector.

        Example:
            >>> vectors = np.random.rand(100, 768)
            >>> metadata = [{"id": i, "text": f"item_{i}"} for i in range(100)]
            >>> index.add_vectors(vectors, metadata)
        """
        if vectors.shape[1] != self.dimension:
            raise ValueError(
                f"Vector dimension {vectors.shape[1]} does not match index dimension {self.dimension}"
            )

        vectors = vectors.astype(np.float32)
        self.index.add(vectors)

        if metadata is not None:
            if len(metadata) != len(vectors):
                raise ValueError("Metadata length must match number of vectors")
            self.metadata.extend(metadata)
        else:
            self.metadata.extend([{}] * len(vectors))

        logger.info(f"Added {len(vectors)} vectors to index (total: {self.index.ntotal})")

    def search(
        self, query_vectors: np.ndarray, k: int = 10
    ) -> tuple[np.ndarray, np.ndarray, List[List[Dict[str, Any]]]]:
        """
        Search for k nearest neighbors.

        Args:
            query_vectors: Query vectors of shape (n_queries, dimension).
            k: Number of nearest neighbors to return.

        Returns:
            Tuple of (distances, indices, metadata_results).

        Example:
            >>> query = np.random.rand(1, 768)
            >>> distances, indices, metadata = index.search(query, k=5)
            >>> top_result = metadata[0][0]
        """
        # Ensure k doesn't exceed index size
        actual_k = min(k, self.index.ntotal) if self.index.ntotal > 0 else k
        if actual_k <= 0:
            raise ValueError("Cannot search empty index")

        query_vectors = query_vectors.astype(np.float32)
        distances, indices = self.index.search(query_vectors, actual_k)

        # Retrieve metadata for results
        metadata_results = []
        for idx_list in indices:
            meta_list = []
            for idx in idx_list:
                if 0 <= idx < len(self.metadata):
                    meta_list.append(self.metadata[idx])
                else:
                    meta_list.append({})
            metadata_results.append(meta_list)

        logger.debug(f"Searched {len(query_vectors)} queries, k={k}")
        return distances, indices, metadata_results

    def save(self, path: str):
        """
        Save index and metadata to disk.

        Args:
            path: Path to save the index (without extension).

        Example:
            >>> index.save("data/index/lemmas")
        """
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)

        # Save FAISS index
        index_path = path.with_suffix(".faiss")
        if self.use_gpu:
            # Transfer to CPU before saving
            cpu_index = self.faiss.index_gpu_to_cpu(self.index)
            self.faiss.write_index(cpu_index, str(index_path))
        else:
            self.faiss.write_index(self.index, str(index_path))

        # Save metadata
        metadata_path = path.with_suffix(".pkl")
        with open(metadata_path, "wb") as f:
            pickle.dump(self.metadata, f)

        logger.info(f"Saved index to {index_path} and metadata to {metadata_path}")

    @classmethod
    def load(cls, path: str, use_gpu: bool = False) -> "VectorIndex":
        """
        Load index and metadata from disk.

        Args:
            path: Path to the index (without extension).
            use_gpu: Whether to use GPU acceleration.

        Returns:
            Loaded VectorIndex instance.

        Example:
            >>> index = VectorIndex.load("data/index/lemmas")
        """
        import faiss

        path = Path(path)
        index_path = path.with_suffix(".faiss")
        metadata_path = path.with_suffix(".pkl")

        if not index_path.exists():
            raise FileNotFoundError(f"Index file not found: {index_path}")

        # Load FAISS index
        loaded_index = faiss.read_index(str(index_path))
        dimension = loaded_index.d

        # Create instance
        instance = cls(dimension=dimension, use_gpu=use_gpu)
        instance.index = loaded_index

        if use_gpu and faiss.get_num_gpus() > 0:
            instance.index = faiss.index_cpu_to_gpu(
                faiss.StandardGpuResources(), 0, instance.index
            )

        # Load metadata
        if metadata_path.exists():
            with open(metadata_path, "rb") as f:
                instance.metadata = pickle.load(f)

        logger.info(
            f"Loaded index from {index_path} with {instance.index.ntotal} vectors"
        )
        return instance

    @property
    def size(self) -> int:
        """Return the number of vectors in the index."""
        return self.index.ntotal
