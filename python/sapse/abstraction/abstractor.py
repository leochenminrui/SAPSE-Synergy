"""Lemma abstraction using RAG and LLM generation."""

import os
import json
import urllib.request
import urllib.error
from typing import Dict, List, Optional

from loguru import logger

from .rag_templates import RAGTemplateManager, load_rag_template_robust

# Import sanitizer if available
try:
    from ..verify.coq_sanitize import sanitize_coq
except ImportError:
    def sanitize_coq(code: str) -> str:
        return code


class LemmaAbstractor:
    """
    Generates parameterized Coq lemmas from NL proof steps using RAG.

    Example:
        >>> abstractor = LemmaAbstractor(template_manager, llm_generator)
        >>> lemma = abstractor.abstract_step(nl_step, retrieved_lemmas)
        >>> print(lemma["draft"])
    """

    def __init__(
        self,
        template_manager: RAGTemplateManager,
        llm_generator=None,
        template_name: str = "default",
    ):
        """
        Initialize lemma abstractor.

        Args:
            template_manager: RAGTemplateManager instance.
            llm_generator: LLM generation function (prompt: str) -> str.
            template_name: Name of template to use.
        """
        self.template_manager = template_manager
        self.llm_generator = llm_generator or self._default_llm_generator
        self.template_name = template_name

        logger.info(f"Initialized LemmaAbstractor with template '{template_name}'")

    def abstract_step(
        self,
        nl_step: str,
        retrieved_lemmas: List[Dict[str, str]],
        metadata: Optional[Dict] = None,
    ) -> Dict[str, str]:
        """
        Abstract a natural language step to a Coq lemma draft.

        Args:
            nl_step: Natural language proof step.
            retrieved_lemmas: List of similar lemmas from retrieval.
            metadata: Optional metadata to include in result.

        Returns:
            Dictionary with 'nl_step', 'draft', 'prompt', and metadata.

        Example:
            >>> result = abstractor.abstract_step(
            ...     "By commutativity of addition",
            ...     [{"name": "plus_comm", "text": "forall a b, a + b = b + a"}]
            ... )
            >>> result["draft"]
        """
        # Format retrieved lemmas
        lemmas_context = self.template_manager.format_retrieved_lemmas(
            retrieved_lemmas
        )

        # Render prompt
        prompt = self.template_manager.render(
            self.template_name,
            {
                "NL_STEP": nl_step,
                "RETRIEVED_LEMMAS": lemmas_context,
            },
        )

        # Generate lemma draft
        lemma_draft = self.llm_generator(prompt)

        # Build result
        result = {
            "nl_step": nl_step,
            "draft": lemma_draft.strip(),
            "prompt": prompt,
            "retrieved_count": len(retrieved_lemmas),
        }

        if metadata:
            result.update(metadata)

        logger.debug(f"Generated lemma draft for step: {nl_step[:50]}...")
        return result

    def abstract_batch(
        self,
        nl_steps: List[str],
        retrieved_lemmas_list: List[List[Dict[str, str]]],
    ) -> List[Dict[str, str]]:
        """
        Abstract multiple steps in batch.

        Args:
            nl_steps: List of NL steps.
            retrieved_lemmas_list: List of retrieved lemmas for each step.

        Returns:
            List of lemma draft dictionaries.

        Example:
            >>> results = abstractor.abstract_batch(steps, retrieved)
        """
        if len(nl_steps) != len(retrieved_lemmas_list):
            raise ValueError("Length mismatch between steps and retrieved lemmas")

        results = []
        for nl_step, retrieved in zip(nl_steps, retrieved_lemmas_list):
            result = self.abstract_step(nl_step, retrieved)
            results.append(result)

        logger.info(f"Abstracted {len(results)} steps in batch")
        return results

    @staticmethod
    def _default_llm_generator(prompt: str) -> str:
        """
        Default placeholder LLM generator with improved type annotations.

        Returns a well-typed polymorphic lemma. Should be replaced with actual LLM API.

        Args:
            prompt: RAG prompt.

        Returns:
            Generated lemma text (placeholder, type-annotated).
        """
        logger.warning(
            "Using placeholder LLM generator. Replace with actual LLM API."
        )
        # Use sanitizer to ensure proper typing
        return sanitize_coq("Lemma placeholder: forall x, x = x.\nProof. reflexivity. Qed.")


def create_llm_generator(provider: str = "openai", **kwargs):
    """
    Factory function to create LLM generator.

    Args:
        provider: LLM provider ('openai', 'deepseek', 'anthropic', etc.).
        **kwargs: Provider-specific arguments (api_key, model, etc.).

    Returns:
        Generator function (prompt: str) -> str.

    Example:
        >>> generator = create_llm_generator("openai", api_key="...", model="gpt-4")
        >>> result = generator("Generate a lemma for ...")
        >>> generator = create_llm_generator("deepseek")  # Uses env var DEEPSEEK_API_KEY
    """
    if provider == "openai":
        return _create_openai_generator(**kwargs)
    elif provider == "deepseek":
        return _create_deepseek_generator(**kwargs)
    else:
        logger.warning(f"Unknown provider '{provider}', using placeholder")
        return LemmaAbstractor._default_llm_generator


def _create_openai_generator(
    api_key: str = None, model: str = "gpt-4", temperature: float = 0.3
):
    """Create OpenAI LLM generator."""
    try:
        import openai

        client = openai.OpenAI(api_key=api_key)
    except ImportError:
        logger.error("openai package not installed")
        return LemmaAbstractor._default_llm_generator

    def generator(prompt: str) -> str:
        try:
            response = client.chat.completions.create(
                model=model,
                messages=[
                    {
                        "role": "system",
                        "content": "You are an expert in Coq theorem proving.",
                    },
                    {"role": "user", "content": prompt},
                ],
                temperature=temperature,
            )
            return response.choices[0].message.content
        except Exception as e:
            logger.error(f"OpenAI API error: {e}")
            return "Lemma error: True.\nProof. trivial. Qed."

    logger.info(f"Created OpenAI generator with model={model}")
    return generator


def _create_deepseek_generator(
    api_key: str = None,
    model: str = None,
    endpoint: str = None,
    temperature: float = 0.2,
    max_tokens: int = 512
):
    """
    Create DeepSeek LLM generator.

    Args:
        api_key: DeepSeek API key (defaults to DEEPSEEK_API_KEY env var).
        model: Model name (defaults to DEEPSEEK_MODEL env var or "deepseek-chat").
        endpoint: API endpoint (defaults to DEEPSEEK_ENDPOINT env var).
        temperature: Sampling temperature.
        max_tokens: Maximum tokens to generate.

    Returns:
        Generator function with sanitized output.

    Example:
        >>> os.environ["DEEPSEEK_API_KEY"] = "sk-..."
        >>> generator = _create_deepseek_generator()
        >>> lemma = generator("Generate commutativity lemma")
    """
    # Get configuration from environment or arguments
    api_key = api_key or os.environ.get("DEEPSEEK_API_KEY")
    model = model or os.environ.get("DEEPSEEK_MODEL", "deepseek-chat")
    endpoint = endpoint or os.environ.get(
        "DEEPSEEK_ENDPOINT",
        "https://api.deepseek.com/chat/completions"
    )

    if not api_key:
        logger.warning("DEEPSEEK_API_KEY not set, using fallback generator")
        return LemmaAbstractor._default_llm_generator

    def generator(prompt: str) -> str:
        """Generate Coq lemma using DeepSeek API."""
        try:
            # Prepare request
            data = {
                "model": model,
                "messages": [{"role": "user", "content": prompt}],
                "temperature": temperature,
                "max_tokens": max_tokens
            }

            req = urllib.request.Request(
                endpoint,
                data=json.dumps(data).encode("utf-8"),
                headers={
                    "Content-Type": "application/json",
                    "Authorization": f"Bearer {api_key}"
                },
                method="POST"
            )

            # Make API call
            with urllib.request.urlopen(req, timeout=30) as resp:
                payload = json.loads(resp.read().decode("utf-8"))

            # Extract response text
            text = (
                payload.get("choices", [{}])[0]
                .get("message", {})
                .get("content", "")
            ).strip()

            if not text:
                logger.warning("Empty response from DeepSeek, using fallback")
                return LemmaAbstractor._default_llm_generator(prompt)

            # Sanitize the generated code
            sanitized = sanitize_coq(text)
            logger.debug(f"Generated and sanitized lemma via DeepSeek")
            return sanitized

        except urllib.error.URLError as e:
            logger.error(f"DeepSeek API network error: {e}")
            return LemmaAbstractor._default_llm_generator(prompt)
        except Exception as e:
            logger.error(f"DeepSeek API error: {e}")
            return LemmaAbstractor._default_llm_generator(prompt)

    logger.info(f"Created DeepSeek generator with model={model}")
    return generator
