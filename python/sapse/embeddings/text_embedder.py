"""Base text embedder interface."""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import List

import numpy as np
from loguru import logger


class TextEmbedder(ABC):
    """
    Abstract base class for text embedders.

    All embedding backends must implement the embed_texts method.

    Example:
        >>> class MyEmbedder(TextEmbedder):
        ...     def embed_texts(self, texts):
        ...         return np.random.rand(len(texts), 768)
        >>> embedder = MyEmbedder()
        >>> vectors = embedder.embed_texts(["hello", "world"])
        >>> vectors.shape
        (2, 768)
    """

    def __init__(self, cache_dir: str = None):
        """
        Initialize text embedder.

        Args:
            cache_dir: Directory for caching embeddings. Defaults to ~/.cache/sapse/
        """
        if cache_dir is None:
            cache_dir = Path.home() / ".cache" / "sapse"
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        logger.debug(f"Initialized embedder with cache dir: {self.cache_dir}")

    @abstractmethod
    def embed_texts(self, texts: List[str]) -> np.ndarray:
        """
        Embed a list of texts into vectors.

        Args:
            texts: List of text strings to embed.

        Returns:
            numpy array of shape (len(texts), embedding_dim).

        Example:
            >>> vectors = embedder.embed_texts(["text1", "text2"])
            >>> vectors.shape
            (2, 768)
        """
        pass

    @property
    @abstractmethod
    def embedding_dim(self) -> int:
        """Return the dimension of the embeddings."""
        pass

    def embed_single(self, text: str) -> np.ndarray:
        """
        Embed a single text.

        Args:
            text: Text string to embed.

        Returns:
            1D numpy array of embedding.

        Example:
            >>> vector = embedder.embed_single("hello world")
            >>> vector.shape
            (768,)
        """
        return self.embed_texts([text])[0]

    def batch_embed(
        self, texts: List[str], batch_size: int = 32
    ) -> np.ndarray:
        """
        Embed texts in batches for efficiency.

        Args:
            texts: List of texts to embed.
            batch_size: Number of texts per batch.

        Returns:
            numpy array of embeddings.

        Example:
            >>> vectors = embedder.batch_embed(texts, batch_size=16)
        """
        # Handle edge case: empty input
        if not texts:
            return np.empty((0, self.get_dimension()), dtype=np.float32)

        all_embeddings = []

        for i in range(0, len(texts), batch_size):
            batch = texts[i : i + batch_size]
            embeddings = self.embed_texts(batch)
            all_embeddings.append(embeddings)
            logger.debug(
                f"Embedded batch {i // batch_size + 1}/{(len(texts) - 1) // batch_size + 1}"
            )

        return np.vstack(all_embeddings)
