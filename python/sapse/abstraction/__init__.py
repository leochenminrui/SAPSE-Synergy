"""RAG-based lemma abstraction and generation."""

from .abstractor import LemmaAbstractor, create_llm_generator
from .rag_templates import (
    DEFAULT_RAG_TEMPLATE_EN,
    DEFAULT_RAG_TEMPLATE_ZH,
    PromptTemplate,
    RAGTemplateManager,
)

__all__ = [
    "PromptTemplate",
    "RAGTemplateManager",
    "LemmaAbstractor",
    "create_llm_generator",
    "DEFAULT_RAG_TEMPLATE_EN",
    "DEFAULT_RAG_TEMPLATE_ZH",
]
