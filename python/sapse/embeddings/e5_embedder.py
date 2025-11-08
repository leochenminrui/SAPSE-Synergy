"""E5 embedding backend using sentence-transformers."""

from typing import List

import numpy as np
from loguru import logger

from .text_embedder import TextEmbedder


class E5Embedder(TextEmbedder):
    """
    E5 embedding backend (intfloat/e5-base-v2).

    Uses sentence-transformers for local embedding generation.

    Example:
        >>> embedder = E5Embedder()
        >>> vectors = embedder.embed_texts(["query: hello", "passage: world"])
        >>> vectors.shape
        (2, 768)
    """

    def __init__(
        self,
        model_name: str = "intfloat/e5-base-v2",
        cache_dir: str = None,
        device: str = None,
    ):
        """
        Initialize E5 embedder.

        Args:
            model_name: HuggingFace model name.
            cache_dir: Cache directory for models and embeddings.
            device: Device to use ('cpu', 'cuda', or None for auto).
        """
        super().__init__(cache_dir)

        try:
            from sentence_transformers import SentenceTransformer
        except ImportError:
            logger.error(
                "sentence-transformers not installed. Run: pip install sentence-transformers"
            )
            raise

        self.model_name = model_name
        self.model = SentenceTransformer(
            model_name, cache_folder=str(self.cache_dir / "models"), device=device
        )
        self._embedding_dim = self.model.get_sentence_embedding_dimension()

        logger.info(
            f"Initialized E5 embedder: {model_name}, dim={self._embedding_dim}"
        )

    @property
    def embedding_dim(self) -> int:
        """Return embedding dimension."""
        return self._embedding_dim

    def embed_texts(self, texts: List[str]) -> np.ndarray:
        """
        Embed texts using E5 model.

        Args:
            texts: List of texts to embed. For best results, prefix with
                   "query: " or "passage: " as appropriate.

        Returns:
            numpy array of embeddings.

        Example:
            >>> texts = ["query: " + q for q in queries]
            >>> vectors = embedder.embed_texts(texts)
        """
        if not texts:
            return np.array([])

        embeddings = self.model.encode(
            texts,
            convert_to_numpy=True,
            show_progress_bar=False,
            normalize_embeddings=True,
        )

        logger.debug(f"Embedded {len(texts)} texts with E5")
        return embeddings.astype(np.float32)
