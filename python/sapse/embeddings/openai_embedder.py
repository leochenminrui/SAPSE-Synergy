"""OpenAI embedding backend."""

import time
from typing import List

import numpy as np
from loguru import logger

from .text_embedder import TextEmbedder


class OpenAIEmbedder(TextEmbedder):
    """
    OpenAI text-embedding-3-large backend.

    Requires OPENAI_API_KEY environment variable.

    Example:
        >>> embedder = OpenAIEmbedder(api_key="sk-...")
        >>> vectors = embedder.embed_texts(["hello", "world"])
        >>> vectors.shape
        (2, 3072)
    """

    def __init__(
        self,
        api_key: str = None,
        model: str = "text-embedding-3-large",
        cache_dir: str = None,
        max_retries: int = 3,
    ):
        """
        Initialize OpenAI embedder.

        Args:
            api_key: OpenAI API key. If None, loads from environment.
            model: Model name (default: text-embedding-3-large).
            cache_dir: Cache directory for embeddings.
            max_retries: Maximum number of retry attempts on failure.
        """
        super().__init__(cache_dir)

        try:
            import openai

            self.client = openai.OpenAI(api_key=api_key)
        except ImportError:
            logger.error("openai package not installed. Run: pip install openai")
            raise

        self.model = model
        self.max_retries = max_retries
        self._embedding_dim = 3072 if "large" in model else 1536

        logger.info(f"Initialized OpenAI embedder with model: {model}")

    @property
    def embedding_dim(self) -> int:
        """Return embedding dimension."""
        return self._embedding_dim

    def embed_texts(self, texts: List[str]) -> np.ndarray:
        """
        Embed texts using OpenAI API.

        Args:
            texts: List of texts to embed.

        Returns:
            numpy array of embeddings.

        Example:
            >>> vectors = embedder.embed_texts(["text1", "text2"])
        """
        if not texts:
            return np.array([])

        for attempt in range(self.max_retries):
            try:
                response = self.client.embeddings.create(
                    input=texts, model=self.model
                )

                embeddings = [item.embedding for item in response.data]
                return np.array(embeddings, dtype=np.float32)

            except Exception as e:
                logger.warning(
                    f"OpenAI API error (attempt {attempt + 1}/{self.max_retries}): {e}"
                )
                if attempt < self.max_retries - 1:
                    time.sleep(2**attempt)  # Exponential backoff
                else:
                    logger.error("Max retries reached, falling back to zeros")
                    return np.zeros((len(texts), self.embedding_dim), dtype=np.float32)
