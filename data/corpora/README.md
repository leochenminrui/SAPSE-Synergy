# Corpora Directory

## Why This Directory Is Empty

The `corpora/` directory is **intentionally empty** in the artifact release for the following reasons:

### 1. **Licensing Constraints**

The original corpora include:
- **CompCert**: INRIA Non-Commercial License (cannot redistribute)
- **Coq Standard Library**: LGPL 2.1 (large, ~100 MB)
- **Coq-ext-lib**: MIT (redistributable but large)

To avoid licensing issues and keep the artifact size manageable, we **do not redistribute** the raw corpora.

### 2. **Pre-Extracted Data Provided**

Instead of raw corpora, the artifact includes the **essential pre-processed data**:

#### ✅ **FAISS Index** (`data/index/coq_lemmas_e5.faiss`)
- **Size**: 21 MB
- **Content**: 7,200+ verified lemmas embedded with E5-base-v2
- **Purpose**: Semantic retrieval for RAG prompting
- **Status**: Ready to use, no extraction needed

#### ✅ **Metadata** (`data/index/coq_lemmas_e5.pkl`)
- **Size**: 3.8 MB
- **Content**: Lemma names, text, and source information
- **Purpose**: Mapping from FAISS vectors to actual lemma text
- **Status**: Ready to use

#### ✅ **Input Dataset** (`data/input/synergy_rag_2k.jsonl`)
- **Size**: 2.1 MB
- **Content**: 2,000 lemma drafts generated from neural RAG
- **Purpose**: Main experiment input
- **Status**: Ready to use

### 3. **No Extraction Required**

The artifact is **self-contained** and does not require:
- Downloading CompCert, Coq-std-lib, or Coq-ext-lib
- Extracting lemmas from .v files
- Building FAISS indices from scratch
- Any preprocessing steps

All necessary data is **pre-computed and included** in `data/index/` and `data/input/`.

---

## For Researchers Who Want the Raw Corpora

If you want to rebuild the FAISS index from scratch or explore the original corpora:

### Download Original Sources

```bash
# CompCert (INRIA Non-Commercial License - for research use only)
git clone https://github.com/AbsInt/CompCert.git

# Coq Standard Library (included with Coq installation)
opam install coq.9.1.0

# Coq-ext-lib (MIT License)
git clone https://github.com/coq-community/coq-ext-lib.git
```

### Extract Lemmas

Use the extraction script from the main SAPSE repository:

```bash
# From parent SAPSE repository (not included in artifact)
python scripts/extract_lemmas_from_corpus.py \
  --corpus CompCert/ \
  --output extracted_lemmas.jsonl
```

### Rebuild FAISS Index

```bash
# From artifact_release/python/
python scripts/build_index.py \
  --input extracted_lemmas.jsonl \
  --embedder e5 \
  --output ../data/index/coq_lemmas_e5
```

**Note**: This is **not required** for artifact evaluation. The pre-built index is sufficient for all experiments.

---

## What's Included vs. What's Not

### ✅ **Included in Artifact**
- FAISS index (7,200 lemmas, E5 embeddings)
- Metadata (lemma names and text)
- 2,000 lemma drafts for experiments
- All experiment results
- Complete Python pipeline
- Mechanized Coq proofs

### ❌ **Not Included** (Not Needed)
- Raw CompCert source code (~500 MB)
- Raw Coq Standard Library (~100 MB)
- Raw Coq-ext-lib source (~50 MB)
- Intermediate extraction files
- Multiple embedding models (only E5 included)

---

## Directory Structure (Minimal)

The `data/` directory contains only what's needed:

```
data/
├── corpora/              # Empty (raw sources not needed)
├── index/                # Pre-built FAISS index
│   ├── coq_lemmas_e5.faiss   (21 MB)
│   └── coq_lemmas_e5.pkl     (3.8 MB)
├── input/                # Experiment input
│   └── synergy_rag_2k.jsonl  (2.1 MB)
└── samples/              # Small test datasets
```

**Total data size**: ~27 MB (manageable for Zenodo and GitHub)

---

## Frequently Asked Questions

### Q: Do I need to download corpora to run experiments?
**A**: No. The pre-built FAISS index in `data/index/` contains everything needed.

### Q: Can I reproduce the FAISS index from scratch?
**A**: Yes, but it's not required. Download the original corpora and use the extraction/indexing scripts from the main SAPSE repository.

### Q: Why not include CompCert directly?
**A**: CompCert has a non-commercial license that restricts redistribution. We include only the extracted, derived data (lemma text and embeddings), which is permitted for research use.

### Q: How were the 7,200 lemmas selected?
**A**: All verified lemmas (theorems, lemmas) from CompCert, Coq-std-lib, and Coq-ext-lib were extracted, filtered for well-formedness, and indexed.

---

## License Information

### Included Data (FAISS Index)
- **License**: Derived from INRIA, LGPL, and MIT sources
- **Purpose**: Research and evaluation only
- **Redistribution**: Metadata and embeddings included; raw sources not redistributed

### Original Corpora (Not Included)
- **CompCert**: INRIA Non-Commercial License
- **Coq Standard Library**: LGPL 2.1
- **Coq-ext-lib**: MIT License

By using the pre-built index, you comply with all licensing requirements.

---

## Summary

**The `corpora/` directory is intentionally empty.**

All necessary data is pre-computed and included in:
- `data/index/` - FAISS index and metadata (24.8 MB)
- `data/input/` - Experiment input (2.1 MB)

**No additional downloads or preprocessing required** for artifact evaluation.

---

**Last Updated**: 2025-11-08
**Artifact Version**: 1.0.0
