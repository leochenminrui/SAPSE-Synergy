"""RAG prompt templates for lemma abstraction."""

from pathlib import Path
from typing import Dict, List

from loguru import logger


class PromptTemplate:
    """
    Template for RAG prompts with placeholder substitution.

    Example:
        >>> template = PromptTemplate("Hello {{NAME}}, your age is {{AGE}}.")
        >>> rendered = template.render({"NAME": "Alice", "AGE": "25"})
        >>> print(rendered)
        Hello Alice, your age is 25.
    """

    def __init__(self, template_str: str):
        """
        Initialize prompt template.

        Args:
            template_str: Template string with {{PLACEHOLDER}} markers.
        """
        self.template_str = template_str

    def render(self, variables: Dict[str, str]) -> str:
        """
        Render template with variable substitution.

        Args:
            variables: Dictionary mapping placeholder names to values.

        Returns:
            Rendered template string.

        Example:
            >>> template.render({"NL_STEP": "By induction"})
        """
        result = self.template_str
        for key, value in variables.items():
            placeholder = f"{{{{{key}}}}}"
            result = result.replace(placeholder, str(value))
        return result

    @classmethod
    def from_file(cls, file_path: str) -> "PromptTemplate":
        """
        Load template from file.

        Args:
            file_path: Path to template file.

        Returns:
            PromptTemplate instance.

        Example:
            >>> template = PromptTemplate.from_file("prompts/rag_prompt_en.txt")
        """
        path = Path(file_path)
        if not path.exists():
            logger.warning(f"Template file {file_path} not found")
            return cls("")

        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        logger.info(f"Loaded template from {file_path}")
        return cls(content)


class RAGTemplateManager:
    """
    Manager for multiple RAG prompt templates.

    Example:
        >>> manager = RAGTemplateManager()
        >>> manager.load_template("abstraction", "prompts/rag_prompt_en.txt")
        >>> prompt = manager.render("abstraction", {"NL_STEP": "..."})
    """

    def __init__(self):
        """Initialize template manager."""
        self.templates: Dict[str, PromptTemplate] = {}
        logger.debug("Initialized RAGTemplateManager")

    def load_template(self, name: str, file_path: str):
        """
        Load a template from file.

        Args:
            name: Template name/identifier.
            file_path: Path to template file.

        Example:
            >>> manager.load_template("en", "prompts/rag_prompt_en.txt")
        """
        template = PromptTemplate.from_file(file_path)
        self.templates[name] = template
        logger.info(f"Loaded template '{name}' from {file_path}")

    def add_template(self, name: str, template_str: str):
        """
        Add a template from string.

        Args:
            name: Template name/identifier.
            template_str: Template string.

        Example:
            >>> manager.add_template("simple", "Generate lemma for: {{NL_STEP}}")
        """
        self.templates[name] = PromptTemplate(template_str)

    def render(self, name: str, variables: Dict[str, str]) -> str:
        """
        Render a template by name.

        Args:
            name: Template name.
            variables: Variable substitutions.

        Returns:
            Rendered prompt.

        Example:
            >>> prompt = manager.render("en", {"NL_STEP": "By induction"})
        """
        if name not in self.templates:
            logger.warning(f"Template '{name}' not found, using empty template")
            return ""

        return self.templates[name].render(variables)

    def format_retrieved_lemmas(self, lemmas: List[Dict[str, str]]) -> str:
        """
        Format retrieved lemmas for RAG context.

        Args:
            lemmas: List of lemma dicts with 'name', 'text', 'score' keys.

        Returns:
            Formatted string of lemmas.

        Example:
            >>> context = manager.format_retrieved_lemmas(results)
        """
        if not lemmas:
            return "No similar lemmas found."

        formatted = []
        for i, lemma in enumerate(lemmas, 1):
            name = lemma.get("name", f"lemma_{i}")
            text = lemma.get("text", "")
            score = lemma.get("score", 0.0)

            formatted.append(f"{i}. {name} (similarity: {score:.2f})\n   {text}")

        return "\n\n".join(formatted)


# Default template strings
DEFAULT_RAG_TEMPLATE_EN = """SYSTEM INSTRUCTIONS (Coq lemma abstraction)

You MUST return a SINGLE Coq lemma (and its proof) with EXPLICIT TYPES for ALL quantified variables.
If a variable type cannot be inferred from context, prefer a POLYMORPHIC fallback:
  forall (A : Type) (x : A), ...
If domain evidence suggests arithmetic (plus, mult, le, lt), prefer explicit nat types:
  forall (x y : nat), ...
Return ONLY Coq code. No comments, no prose. End with "Qed.".

TASK INPUT
{{NL_STEP}}

RETRIEVED HINTS (semantically similar lemmas)
{{RETRIEVED_LEMMAS}}

OUTPUT FORMAT
- A single well-typed Coq lemma + proof that is reusable/parameterized, consistent with the hints.
- Prefer polymorphic forms when domain type is unclear; otherwise use domain-appropriate concrete types (nat/bool/list)."""

DEFAULT_RAG_TEMPLATE_ZH = """给定自然语言证明步骤：
{{NL_STEP}}

以及以下语义相似的Coq引理：
{{RETRIEVED_LEMMAS}}

请生成一个可复用的、参数化的Coq引理，它应该：
1. 足够通用，可在其他证明中复用
2. 使用正确的Coq语法（Lemma name: statement.）
3. 可选地包含简短的证明草图或策略提示

仅输出Coq引理定义，不需要额外解释。"""


def load_rag_template_robust(path: str = None, fallback_name: str = "en", template_variant: str = "default") -> str:
    """
    Load RAG template with robust fallback to default.

    Args:
        path: Path to template file (optional).
        fallback_name: Name of default template to use ("en" or "zh").
        template_variant: Template variant ("default", "dseries_strongtyping").

    Returns:
        Template string (from file or default).

    Example:
        >>> template_str = load_rag_template_robust("prompts/rag_prompt_en.txt")
        >>> template_str = load_rag_template_robust(template_variant="dseries_strongtyping")
    """
    # Handle D-series strong typing variant
    if template_variant == "dseries_strongtyping":
        dseries_path = "prompts/rag_prompt_dseries.txt"
        try:
            template = PromptTemplate.from_file(dseries_path)
            if template.template_str:
                logger.info(f"Loaded D-series template from {dseries_path}")
                return template.template_str
        except Exception as e:
            logger.warning(f"Failed to load D-series template: {e}, falling back to default")

    # Try loading from file first
    if path:
        try:
            template = PromptTemplate.from_file(path)
            if template.template_str:  # Check if file had content
                logger.info(f"Loaded template from {path}")
                return template.template_str
        except Exception as e:
            logger.warning(f"Failed to load template from {path}: {e}, using default")

    # Fall back to in-code default
    if fallback_name == "zh":
        logger.info("Using DEFAULT_RAG_TEMPLATE_ZH")
        return DEFAULT_RAG_TEMPLATE_ZH
    else:
        logger.info("Using DEFAULT_RAG_TEMPLATE_EN")
        return DEFAULT_RAG_TEMPLATE_EN
