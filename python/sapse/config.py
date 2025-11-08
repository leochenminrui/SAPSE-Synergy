"""Configuration management for SAPSE."""

import os
from pathlib import Path
from typing import Any, Dict

import yaml
from loguru import logger


class Config:
    """
    Configuration manager for SAPSE pipeline.

    Loads settings from YAML files and environment variables.

    Example:
        >>> config = Config.from_yaml("configs/default.yaml")
        >>> embedder_type = config.get("embedder.type", "e5")
        >>> top_k = config.get("retrieval.top_k", 10)
    """

    def __init__(self, config_dict: Dict[str, Any] = None):
        """
        Initialize configuration.

        Args:
            config_dict: Configuration dictionary. Defaults to empty dict.
        """
        self._config = config_dict or {}
        self._load_env_vars()

    @classmethod
    def from_yaml(cls, config_path: str) -> "Config":
        """
        Load configuration from YAML file.

        Args:
            config_path: Path to YAML configuration file.

        Returns:
            Config instance.

        Example:
            >>> config = Config.from_yaml("configs/default.yaml")
        """
        path = Path(config_path)
        if not path.exists():
            logger.warning(f"Config file {config_path} not found, using defaults")
            return cls({})

        with open(path) as f:
            config_dict = yaml.safe_load(f) or {}

        logger.info(f"Loaded configuration from {config_path}")
        return cls(config_dict)

    def _load_env_vars(self):
        """Load API keys and sensitive data from environment variables."""
        self._env_keys = {
            "OPENAI_API_KEY": os.getenv("OPENAI_API_KEY"),
            "HF_TOKEN": os.getenv("HF_TOKEN"),
        }

    def get(self, key: str, default: Any = None) -> Any:
        """
        Get configuration value by dot-separated key.

        Args:
            key: Dot-separated key (e.g., "embedder.type").
            default: Default value if key not found.

        Returns:
            Configuration value.

        Example:
            >>> config.get("retrieval.top_k", 10)
            10
        """
        keys = key.split(".")
        value = self._config
        for k in keys:
            if isinstance(value, dict):
                value = value.get(k)
            else:
                return default
            if value is None:
                return default
        return value

    def get_env(self, key: str) -> str:
        """
        Get environment variable value.

        Args:
            key: Environment variable name.

        Returns:
            Environment variable value or empty string.

        Example:
            >>> api_key = config.get_env("OPENAI_API_KEY")
        """
        return self._env_keys.get(key, "")

    def set(self, key: str, value: Any):
        """
        Set configuration value.

        Args:
            key: Dot-separated key.
            value: Value to set.

        Example:
            >>> config.set("retrieval.top_k", 20)
        """
        keys = key.split(".")
        d = self._config
        for k in keys[:-1]:
            if k not in d:
                d[k] = {}
            d = d[k]
        d[keys[-1]] = value

    def to_dict(self) -> Dict[str, Any]:
        """Return configuration as dictionary."""
        return self._config.copy()
