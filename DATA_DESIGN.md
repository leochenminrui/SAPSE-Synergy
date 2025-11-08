# Data Design and Rationale

## Overview

The SAPSE-Synergy artifact uses a **minimal, self-contained data design** that includes only the essential pre-processed data needed for reproducibility.

---

## Design Principle: Pre-Processed, Not Raw

### ✅ What IS Included

1. **FAISS Index** (`data/index/coq_lemmas_e5.faiss`, 21 MB)
   - 7,200+ verified Coq lemmas
   - E5-base-v2 embeddings (768-dim)
   - Ready for semantic retrieval

2. **Metadata** (`data/index/coq_lemmas_e5.pkl`, 3.8 MB)
   - Lemma names, text, and sources
   - Maps FAISS vectors to actual lemmas

3. **Experiment Input** (`data/input/synergy_rag_2k.jsonl`, 2.1 MB)
   - 2,000 neural-generated lemma drafts
   - Pre-generated with DeepSeek RAG
   - No API keys required

4. **Sample Datasets** (`data/samples/`)
   - Small test sets for quick validation

**Total**: ~27 MB

### ❌ What is NOT Included

1. **Raw Corpora** (`data/corpora/` is empty)
   - CompCert source (~500 MB) - INRIA Non-Commercial License
   - Coq Standard Library (~100 MB) - LGPL 2.1
   - Coq-ext-lib (~50 MB) - MIT

2. **Intermediate Files**
   - Extracted lemma lists before indexing
   - Multiple embedding formats (only E5 included)
   - Training/validation splits (not needed)

**Reason**: These would add ~650 MB and are not needed for reproduction.

---

## Rationale

### 1. **Licensing Compliance**

**CompCert** has a non-commercial license that restricts redistribution:
- ❌ Cannot include raw CompCert .v files
- ✅ Can include derived data (lemma text, embeddings) for research

**Solution**: Include only the extracted, processed data.

### 2. **Artifact Size**

Including raw corpora would:
- Increase size from ~35 MB to ~685 MB
- Require Git LFS or multiple archives
- Slow down download for evaluators

**Solution**: Keep artifact under 50 MB for easy distribution.

### 3. **Reproducibility Focus**

For artifact evaluation, reviewers need to:
- ✅ Verify mechanized soundness proofs
- ✅ Run experiments on 2,000 lemmas
- ✅ Compare results with paper numbers
- ❌ NOT rebuild FAISS index from scratch

**Solution**: Include only what's needed for evaluation.

### 4. **Pre-Generated Data**

The 2,000 lemma drafts are **pre-generated**:
- No DeepSeek API key required
- Deterministic reproduction
- Faster evaluation (~3-6 hours vs. ~10+ hours)

**Solution**: Include generated data, not generation scripts.

---

## Data Flow

### Original Pipeline (Not Needed for Artifact)

```
CompCert .v files (500 MB)
    ↓ [extract_lemmas.py]
Extracted lemmas JSONL (50 MB)
    ↓ [embed with E5]
FAISS index (21 MB) ✅ INCLUDED
    ↓ [RAG with DeepSeek]
2,000 lemma drafts (2.1 MB) ✅ INCLUDED
    ↓ [sanitize + verify]
Results CSV (0.5 MB) ✅ INCLUDED
```

### Artifact Pipeline (Self-Contained)

```
FAISS index (21 MB) ✅ PROVIDED
    ↓ [already built]
2,000 lemma drafts (2.1 MB) ✅ PROVIDED
    ↓ [run_full_experiment.sh]
Results CSV (0.5 MB) ✅ GENERATED
    ↓ [analyze_synergy_experiments.py]
Tables + Figures ✅ GENERATED
```

**Key insight**: Start from pre-built index, skip extraction and embedding.

---

## What Evaluators Can Do

### ✅ Fully Reproducible (No Extra Downloads)

1. **Verify Coq proofs** (5 min)
   ```bash
   make -C coq/ -j4
   ```

2. **Run experiments** (3-6 hours)
   ```bash
   bash python/run_full_experiment.sh
   ```

3. **Generate analysis** (2 seconds)
   ```bash
   python python/scripts/analyze_synergy_experiments.py --all
   ```

4. **Compare with paper** (1 min)
   ```bash
   diff outputs/summary.csv outputs/reproduction_run/summary.csv
   ```

**No corpora needed!**

### ⚠️ Partially Reproducible (Requires Downloads)

5. **Rebuild FAISS index** (1-2 hours)
   - Download CompCert (~500 MB)
   - Extract lemmas
   - Embed with E5
   - Build FAISS index

**Not required for evaluation.**

### ❌ Not Reproducible (Requires API Key)

6. **Regenerate 2,000 lemma drafts**
   - Requires DeepSeek API key ($10-20)
   - Requires ~10 hours of API calls
   - Non-deterministic (LLM output varies)

**Not recommended for evaluation.**

---

## Comparison with Other Artifacts

| Approach | Size | Downloads | Time |
|----------|------|-----------|------|
| **Raw Data** | ~685 MB | None | 1-2 hours build |
| **Pre-Processed** (ours) | ~35 MB | None | <5 min build |
| **Scripts Only** | ~5 MB | 700+ MB | 10+ hours build |

**Our choice**: Pre-processed for best evaluator experience.

---

## For Researchers Extending the Work

If you want to modify the corpora or indexing:

### Option 1: Use Provided Index (Recommended)

```bash
# Just modify experiment parameters
cd python/
python scripts/run_synergy_experiments.py \
  --input ../data/input/synergy_rag_2k.jsonl \
  --output-dir ../outputs/my_experiment \
  --top-k 20  # Change retrieval parameter
```

### Option 2: Build New Index

```bash
# 1. Download corpora
git clone https://github.com/AbsInt/CompCert.git
opam install coq.9.1.0

# 2. Extract lemmas (from main SAPSE repo)
python scripts/extract_lemmas.py \
  --corpus CompCert/ \
  --output my_lemmas.jsonl

# 3. Build index
python scripts/build_index.py \
  --input my_lemmas.jsonl \
  --embedder e5 \
  --output my_index
```

### Option 3: Generate New Lemma Drafts

```bash
# Requires DEEPSEEK_API_KEY
export DEEPSEEK_API_KEY="your-key-here"

python scripts/generate_lemma_drafts.py \
  --index ../data/index/coq_lemmas_e5 \
  --output my_drafts.jsonl \
  --count 100
```

---

## Licensing Summary

### Artifact Data
- **FAISS Index**: Derived from INRIA/LGPL/MIT sources, research use only
- **Lemma Drafts**: Neural-generated, MIT License
- **Code**: MIT License

### Original Corpora (Not Included)
- **CompCert**: INRIA Non-Commercial (cannot redistribute)
- **Coq Stdlib**: LGPL 2.1 (can redistribute, but large)
- **Coq-ext-lib**: MIT (can redistribute, but not needed)

**All licensing requirements satisfied** by including only derived data.

---

## FAQ

### Q: Why is `data/corpora/` empty?
**A**: Raw corpora are not needed and would violate CompCert's license. All necessary data is pre-processed in `data/index/`.

### Q: How do I know the index is correct?
**A**: The experiment results match the paper numbers (37.6% → 32.8%), validating the index integrity.

### Q: Can I rebuild the index?
**A**: Yes, but not required. Download corpora separately and use extraction scripts.

### Q: Is the 2,000-lemma dataset the same as in the paper?
**A**: Yes. It's pre-generated with seed=42 for determinism.

### Q: Why not use Git LFS for large files?
**A**: At 27 MB total, the data is small enough for direct inclusion.

---

## Directory Structure Explanation

```
data/
├── corpora/              # Empty by design (see above)
│   └── README.md         # Explains why empty
├── index/                # Pre-built FAISS index (ESSENTIAL)
│   ├── coq_lemmas_e5.faiss   # Vector index (21 MB)
│   └── coq_lemmas_e5.pkl     # Metadata (3.8 MB)
├── input/                # Experiment input (ESSENTIAL)
│   └── synergy_rag_2k.jsonl  # 2,000 lemmas (2.1 MB)
└── samples/              # Small test sets (OPTIONAL)
```

**Only `index/` and `input/` are required for experiments.**

---

## Validation

To verify data integrity:

```bash
# Check dataset size
wc -l data/input/synergy_rag_2k.jsonl
# Expected: 2000

# Check index size
ls -lh data/index/
# Expected: coq_lemmas_e5.faiss (~21 MB), coq_lemmas_e5.pkl (~3.8 MB)

# Load metadata
python3 -c "import pickle; print(len(pickle.load(open('data/index/coq_lemmas_e5.pkl', 'rb'))))"
# Expected: 7200
```

All checks should pass.

---

## Summary

**The empty `corpora/` directory is intentional and correct.**

- ✅ All essential data included (FAISS index, input dataset)
- ✅ Licensing compliant (no CompCert redistribution)
- ✅ Artifact size minimized (~35 MB)
- ✅ Fully self-contained (no downloads needed)
- ✅ Fast evaluation (<5 min setup, 3-6 hours run)

**No action required from evaluators.**

---

**Last Updated**: 2025-11-08
**Artifact Version**: 1.0.0
