"""CodeBERT embedding backend for code and formal language."""

from typing import List

import numpy as np
import torch
from loguru import logger

from .text_embedder import TextEmbedder


class CodeBERTEmbedder(TextEmbedder):
    """
    CodeBERT embedding backend (microsoft/codebert-base).

    Specialized for code and formal language embeddings.

    Example:
        >>> embedder = CodeBERTEmbedder()
        >>> vectors = embedder.embed_texts(["def foo(): pass", "Lemma test: True."])
        >>> vectors.shape
        (2, 768)
    """

    def __init__(
        self,
        model_name: str = "microsoft/codebert-base",
        cache_dir: str = None,
        device: str = None,
    ):
        """
        Initialize CodeBERT embedder.

        Args:
            model_name: HuggingFace model name (codebert-base or graphcodebert-base).
            cache_dir: Cache directory for models.
            device: Device to use ('cpu', 'cuda', or None for auto).
        """
        super().__init__(cache_dir)

        try:
            from transformers import AutoModel, AutoTokenizer
        except ImportError:
            logger.error("transformers not installed. Run: pip install transformers")
            raise

        self.model_name = model_name
        self.device = device or ("cuda" if torch.cuda.is_available() else "cpu")

        self.tokenizer = AutoTokenizer.from_pretrained(
            model_name, cache_dir=str(self.cache_dir / "models")
        )
        self.model = AutoModel.from_pretrained(
            model_name, cache_dir=str(self.cache_dir / "models")
        )
        self.model.to(self.device)
        self.model.eval()

        self._embedding_dim = self.model.config.hidden_size

        logger.info(
            f"Initialized CodeBERT embedder: {model_name}, dim={self._embedding_dim}, device={self.device}"
        )

    @property
    def embedding_dim(self) -> int:
        """Return embedding dimension."""
        return self._embedding_dim

    def embed_texts(self, texts: List[str]) -> np.ndarray:
        """
        Embed texts using CodeBERT.

        Args:
            texts: List of code or formal language texts.

        Returns:
            numpy array of embeddings.

        Example:
            >>> vectors = embedder.embed_texts(["def f(x): return x*2"])
        """
        if not texts:
            return np.array([])

        embeddings = []

        with torch.no_grad():
            # Tokenize
            encoded = self.tokenizer(
                texts,
                padding=True,
                truncation=True,
                max_length=512,
                return_tensors="pt",
            )
            encoded = {k: v.to(self.device) for k, v in encoded.items()}

            # Get embeddings (use [CLS] token)
            outputs = self.model(**encoded)
            cls_embeddings = outputs.last_hidden_state[:, 0, :]
            embeddings = cls_embeddings.cpu().numpy()

        logger.debug(f"Embedded {len(texts)} texts with CodeBERT")
        return embeddings.astype(np.float32)
