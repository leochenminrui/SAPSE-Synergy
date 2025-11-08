"""Main SAPSE pipeline orchestrator."""

from pathlib import Path
from typing import Any, Dict, List, Optional

import numpy as np
from loguru import logger

from .abstraction import LemmaAbstractor, RAGTemplateManager
from .config import Config
from .datasets import DatasetLoader
from .dedup import NearDuplicateDetector
from .embeddings import CodeBERTEmbedder, E5Embedder, OpenAIEmbedder
from .io_coq import CoqLemmaParser
from .io_nl import NLProofParser
from .retrieval import SemanticSearcher, VectorIndex
from .verify import PipelineMetrics, create_verifier


class SAPSEPipeline:
    """
    Main SAPSE pipeline orchestrator.

    Coordinates all stages: embedding → retrieval → abstraction → deduplication → verification.

    Example:
        >>> config = Config.from_yaml("configs/default.yaml")
        >>> pipeline = SAPSEPipeline(config)
        >>> results = pipeline.run("data/samples/nl_proofs.jsonl")
    """

    def __init__(self, config: Config):
        """
        Initialize SAPSE pipeline.

        Args:
            config: Configuration object.
        """
        self.config = config
        self.metrics = PipelineMetrics()

        # Initialize components
        self.embedder = self._create_embedder()
        self.index = None
        self.searcher = None
        self.template_manager = self._create_template_manager()
        self.abstractor = self._create_abstractor()
        self.dedup_detector = self._create_dedup_detector()
        self.verifier = self._create_verifier()

        self.nl_parser = NLProofParser()
        self.coq_parser = CoqLemmaParser()

        logger.info("Initialized SAPSE pipeline")

    def _create_embedder(self):
        """Create embedder based on config."""
        embedder_type = self.config.get("embedder.type", "e5").lower()
        cache_dir = self.config.get("embedder.cache_dir", None)

        if embedder_type == "openai":
            api_key = self.config.get_env("OPENAI_API_KEY")
            model = self.config.get("embedder.model", "text-embedding-3-large")
            return OpenAIEmbedder(api_key=api_key, model=model, cache_dir=cache_dir)

        elif embedder_type == "e5":
            model = self.config.get("embedder.model", "intfloat/e5-base-v2")
            return E5Embedder(model_name=model, cache_dir=cache_dir)

        elif embedder_type == "codebert":
            model = self.config.get("embedder.model", "microsoft/codebert-base")
            return CodeBERTEmbedder(model_name=model, cache_dir=cache_dir)

        else:
            logger.warning(f"Unknown embedder type '{embedder_type}', defaulting to E5")
            return E5Embedder(cache_dir=cache_dir)

    def _create_template_manager(self):
        """Create RAG template manager."""
        manager = RAGTemplateManager()

        # Load templates
        prompt_en = self.config.get("prompts.rag_en", "prompts/rag_prompt_en.txt")
        prompt_zh = self.config.get("prompts.rag_zh", "prompts/rag_prompt_zh.txt")

        if Path(prompt_en).exists():
            manager.load_template("en", prompt_en)
            # Also load as 'default' alias
            manager.load_template("default", prompt_en)
        if Path(prompt_zh).exists():
            manager.load_template("zh", prompt_zh)

        # Add default template if none loaded
        if not manager.templates:
            from .abstraction import DEFAULT_RAG_TEMPLATE_EN

            manager.add_template("default", DEFAULT_RAG_TEMPLATE_EN)

        return manager

    def _create_abstractor(self):
        """Create lemma abstractor."""
        template_name = self.config.get("abstraction.template", "default")

        # Create LLM generator if specified
        llm_provider = self.config.get("llm.provider", None)
        if llm_provider:
            from .abstraction import create_llm_generator

            # Get API key based on provider
            api_key_env = self.config.get("llm.api_key_env", "OPENAI_API_KEY")
            api_key = self.config.get_env(api_key_env)
            model = self.config.get("llm.model", "gpt-4")
            temperature = self.config.get("llm.temperature", 0.3)

            llm_gen = create_llm_generator(
                llm_provider,
                api_key=api_key,
                model=model,
                temperature=temperature
            )
        else:
            llm_gen = None

        return LemmaAbstractor(
            self.template_manager, llm_generator=llm_gen, template_name=template_name
        )

    def _create_dedup_detector(self):
        """Create deduplication detector."""
        threshold = self.config.get("dedup.threshold", 0.9)
        use_text = self.config.get("dedup.use_text", True)

        return NearDuplicateDetector(
            similarity_threshold=threshold, use_text_normalization=use_text
        )

    def _create_verifier(self):
        """Create verifier (Coq or mock)."""
        use_mock = self.config.get("verify.use_mock", False)
        coqc_path = self.config.get("verify.coqc_path", "coqc")
        timeout = self.config.get("verify.timeout", 30)

        return create_verifier(
            use_mock=use_mock, coqc_path=coqc_path, timeout=timeout
        )

    def load_index(self, index_path: str):
        """
        Load pre-built FAISS index.

        Args:
            index_path: Path to index file (without extension).

        Example:
            >>> pipeline.load_index("data/index/coq_lemmas")
        """
        self.index = VectorIndex.load(index_path)
        self.searcher = SemanticSearcher(self.index, self.embedder)
        logger.info(f"Loaded index from {index_path}")

    def build_index(self, coq_lemmas_file: str, output_path: str):
        """
        Build FAISS index from Coq lemmas.

        Args:
            coq_lemmas_file: Path to JSONL file with Coq lemmas.
            output_path: Path to save index (without extension).

        Example:
            >>> pipeline.build_index("data/samples/coq_lemmas.jsonl", "data/index/lemmas")
        """
        logger.info(f"Building index from {coq_lemmas_file}")

        # Load lemmas
        loader = DatasetLoader(coq_lemmas_file)
        lemmas = loader.load_all()

        if not lemmas:
            logger.warning("No lemmas found")
            return

        # Extract texts and prepare metadata
        texts = []
        metadata = []
        for lemma in lemmas:
            text = lemma.get("text", "")
            texts.append(text)
            metadata.append(lemma)

        # Embed
        logger.info(f"Embedding {len(texts)} lemmas...")
        vectors = self.embedder.batch_embed(texts, batch_size=32)

        # Create index
        self.index = VectorIndex(dimension=self.embedder.embedding_dim)
        self.index.add_vectors(vectors, metadata)

        # Save
        self.index.save(output_path)
        logger.info(f"Index built and saved to {output_path}")

        # Create searcher
        self.searcher = SemanticSearcher(self.index, self.embedder)

    def run(
        self,
        nl_proofs_file: str,
        output_file: str = "outputs/lemmas_verified.jsonl",
    ) -> List[Dict[str, Any]]:
        """
        Run the full SAPSE pipeline.

        Args:
            nl_proofs_file: Path to NL proofs JSONL file.
            output_file: Path to save verified lemmas.

        Returns:
            List of verified lemma dictionaries.

        Example:
            >>> results = pipeline.run("data/samples/nl_proofs.jsonl")
        """
        if self.searcher is None:
            raise RuntimeError("Index not loaded. Call load_index() or build_index() first.")

        logger.info(f"Running SAPSE pipeline on {nl_proofs_file}")

        # Load NL proofs
        loader = DatasetLoader(nl_proofs_file)
        nl_proofs = loader.load_all()

        all_results = []

        # Process each proof
        for proof_item in nl_proofs:
            proof_id = proof_item.get("id", "unknown")
            nl_proof = proof_item.get("nl_proof", "")

            logger.info(f"Processing proof {proof_id}")

            # Extract steps
            steps = self.nl_parser.extract_steps(nl_proof)

            # Process each step
            for step in steps:
                step_text = step["text"]
                step_id = f"{proof_id}#step{step['step_num']}"

                # Retrieve similar lemmas
                top_k = self.config.get("retrieval.top_k", 10)
                threshold = self.config.get("retrieval.threshold", 0.8)

                retrieved = self.searcher.search_single(step_text, k=top_k)
                retrieved_filtered = [r for r in retrieved if r["score"] >= threshold]

                # Abstract to lemma draft
                lemma_result = self.abstractor.abstract_step(
                    step_text, retrieved_filtered, metadata={"step_id": step_id}
                )

                all_results.append(lemma_result)

        # Deduplication
        logger.info("Deduplicating lemma drafts...")

        # Handle edge case: no drafts generated
        if not all_results:
            logger.warning("No lemma drafts generated - skipping deduplication")
            unique_results = []
        else:
            drafts = [r["draft"] for r in all_results]
            draft_vectors = self.embedder.batch_embed(drafts, batch_size=32)
            unique_indices = self.dedup_detector.deduplicate(draft_vectors, drafts)

            unique_results = [all_results[i] for i in unique_indices]
            logger.info(f"After deduplication: {len(unique_results)} unique lemmas")

        # Verification
        logger.info("Verifying lemmas...")
        for result in unique_results:
            verify_result = self.verifier.verify(result["draft"])
            result["verified"] = verify_result["status"] == "passed"
            result["verify_status"] = verify_result["status"]
            result["verify_message"] = verify_result["message"]

            self.metrics.add_verification_result(verify_result["status"])

        # Save results
        Path(output_file).parent.mkdir(parents=True, exist_ok=True)
        DatasetLoader.save_jsonl(unique_results, output_file)

        logger.info(f"Pipeline complete. Results saved to {output_file}")
        return unique_results

    def get_metrics_summary(self) -> Dict:
        """
        Get metrics summary.

        Returns:
            Metrics dictionary.

        Example:
            >>> summary = pipeline.get_metrics_summary()
            >>> print(summary["conversion_rate"])
        """
        return self.metrics.compute_summary()

    def print_metrics(self):
        """Print metrics summary."""
        self.metrics.print_summary()
