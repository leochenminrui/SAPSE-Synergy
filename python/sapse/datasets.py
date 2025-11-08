"""Dataset utilities for loading and processing data."""

from pathlib import Path
from typing import Any, Dict, Iterator, List

import jsonlines
from loguru import logger


class DatasetLoader:
    """
    Utility for loading JSONL datasets.

    Example:
        >>> loader = DatasetLoader("data/samples/nl_proofs.jsonl")
        >>> for item in loader.iter_items():
        ...     print(item["theorem"])
    """

    def __init__(self, file_path: str):
        """
        Initialize dataset loader.

        Args:
            file_path: Path to JSONL file.
        """
        self.file_path = Path(file_path)
        if not self.file_path.exists():
            logger.warning(f"Dataset file {file_path} does not exist")

    def iter_items(self) -> Iterator[Dict[str, Any]]:
        """
        Iterate over items in the dataset.

        Yields:
            Dictionary items from JSONL file.

        Example:
            >>> for item in loader.iter_items():
            ...     process(item)
        """
        if not self.file_path.exists():
            logger.warning(f"File {self.file_path} not found, skipping")
            return

        with jsonlines.open(self.file_path) as reader:
            for item in reader:
                yield item

    def load_all(self) -> List[Dict[str, Any]]:
        """
        Load all items into memory.

        Returns:
            List of all items.

        Example:
            >>> items = loader.load_all()
            >>> print(f"Loaded {len(items)} items")
        """
        return list(self.iter_items())

    @staticmethod
    def save_jsonl(items: List[Dict[str, Any]], output_path: str):
        """
        Save items to JSONL file.

        Args:
            items: List of dictionary items to save.
            output_path: Output file path.

        Example:
            >>> DatasetLoader.save_jsonl(results, "outputs/results.jsonl")
        """
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        with jsonlines.open(output_path, mode="w") as writer:
            writer.write_all(items)

        logger.info(f"Saved {len(items)} items to {output_path}")
