# SAPSE-Synergy: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Coq](https://img.shields.io/badge/Coq-9.1.0-blue.svg)](https://coq.inria.fr/)
[![Python](https://img.shields.io/badge/Python-3.10+-green.svg)](https://www.python.org/)

**Artifact for FM 2026 Paper**

> **SAPSE-Synergy formalizes a verified bridge between neural lemma generation and Coq proof checking, making the trade-off between soundness and empirical coverage explicit and measurable.**

---

## Overview

This artifact accompanies the FM 2026 paper:

**"SAPSE-Synergy: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving"**

### Three Core Contributions

1. **Mechanically Verified AST Sanitizer** (Rocq 9.1.0)
   - Formally proven sound transformations: require-injection (R_req), binder-normalization (R_bind), and equality canonicalization (R_eq)
   - Full soundness proof in `coq/theories/Soundness.v`
   - Zero `Admitted` proofs - all theorems proven with `Qed`

2. **Retrieval-First Framework**
   - Dual-domain embeddings align neural reasoning with formal Coq lemmas
   - FAISS-powered semantic search over 7,200+ verified lemmas
   - RAG-based lemma generation with DeepSeek/GPT-4

3. **Safety-Coverage Frontier**
   - Quantifies the trade-off between empirical coverage and formal soundness
   - **Baseline-RAG**: 37.6% verified, may include semantically altered lemmas
   - **SAPSE-Synergy**: 32.8% verified, **0 unsafe rewrites**, 98.1% in-fragment
   - Shows that ~5% coverage loss buys complete formal soundness

---

## Quick Start

### Prerequisites

- **Rocq/Coq**: 9.1.0 (for verified core)
- **Python**: ≥ 3.10
- **CoqHammer** (optional): 1.3+ (for hybrid verification)

### Build Verified Core

```bash
# Build all mechanized proofs (5 theories)
cd coq/
make clean && make -j4

# Expected output:
# ROCQ compile theories/Syntax.v
# ROCQ compile theories/Typing.v
# ROCQ compile theories/Semantics.v
# ROCQ compile theories/Sanitizer.v
# ROCQ compile theories/Soundness.v
```

**Verify soundness theorem**:

```bash
grep "Theorem R_AST_sound" coq/theories/Soundness.v
# Expected: Theorem proven with Qed (no Admitted)

# Check for any admitted proofs
grep -r "Admitted\|Axiom" coq/theories/*.v
# Expected: No matches (all proofs complete)
```

### Install Python Dependencies

```bash
cd python/
pip install -r requirements.txt
```

### Run Full Experiment (2,000 Lemmas × 4 Configurations)

```bash
cd python/
bash run_full_experiment.sh

# For quick test (10 lemmas):
bash run_full_experiment.sh --limit 10
```

**Duration**: ~3-6 hours for full 2K experiment (depends on hardware and Coq verification)

---

## Four Experiment Modes

The artifact evaluates four configurations on 2,000 lemma drafts:

| Configuration     | Description                             | Verified% | Unsafe Rewrites |
| ----------------- | --------------------------------------- | --------- | --------------- |
| **Baseline-RAG**  | Direct RAG output, no sanitization      | 37.6%     | (not tracked)   |
| **SAPSE-Strict**  | Verified core only, conservative guards | ~29%      | **0**           |
| **SAPSE-Fast**    | Unverified utility passes, no guards    | 32.8%     | (may be > 0)    |
| **SAPSE-Synergy** | UP preprocessing → VC gatekeeper        | **32.8%** | **0** ✓         |

### What is the Safety-Coverage Frontier?

The **safety-coverage frontier** quantifies the fundamental trade-off in neural theorem proving:

- **Coverage (Y-axis)**: Empirical success rate (% lemmas verified)
- **Safety (X-axis)**: Formal soundness guarantees (0 unsafe rewrites)

**Key Insight**:

- Baseline-RAG achieves **37.6% coverage** but lacks formal soundness guarantees
- SAPSE-Synergy achieves **32.8% coverage** with **0 unsafe rewrites** and **98.1% in-fragment** operation
- The ~5% coverage drop **buys complete mechanized soundness**

This trade-off is **made explicit and measurable** through:

1. Verified Core (VC) passes with soundness proofs
2. Admissibility guards (AdmissibleSpec)
3. Fragment coverage tracking (in-frag vs out-of-frag)

---

## Expected Results

After running the full experiment, you should see results matching Table 2 from the paper:

```
Configuration     | Guards    | Verified (%) | Abstained (%) | Avg Time (s) | URC (Sum)
------------------|-----------|--------------|---------------|--------------|----------
Baseline-RAG      | None      | 37.6 (752)   | ~0            | 0.16         | 0
SAPSE-Strict      | VC-Guarded| ~29 (580)    | ~28           | 0.07         | 0
SAPSE-Fast        | None      | 32.8 (656)   | ~0            | 0.15         | (≥0)
SAPSE-Synergy     | UP→VC     | 32.8 (656)   | ~15           | 0.15         | 0
```

**Key Observations**:

1. SAPSE-Synergy matches Fast in coverage (32.8%) but guarantees URC = 0
2. Strict mode has high abstention (28%) due to conservative guards
3. Synergy balances coverage and safety through UP→VC architecture

---

## Repository Structure

```
sapse-synergy/
├── coq/                          # Rocq 9.1.0 mechanized proofs
│   ├── theories/
│   │   ├── Syntax.v              # AST definition
│   │   ├── Typing.v              # Typing rules
│   │   ├── Semantics.v           # Operational semantics
│   │   ├── Sanitizer.v           # Verified passes (R_req, R_bind, R_eq)
│   │   └── Soundness.v           # Main soundness theorem (R_AST_sound)
│   ├── Makefile
│   └── _CoqProject
│
├── python/                       # Retrieval + sanitizer + verification pipeline
│   ├── sapse/                    # Core library
│   │   ├── embeddings/           # E5, CodeBERT, OpenAI embedders
│   │   ├── retrieval/            # FAISS semantic search
│   │   ├── abstraction/          # RAG-based lemma generation
│   │   ├── sanitize/             # AST sanitization (UP + VC)
│   │   ├── dedup/                # Near-duplicate detection
│   │   └── verify/               # Coq verification
│   ├── scripts/
│   │   ├── run_synergy_experiments.py   # Main experiment runner
│   │   ├── analyze_synergy_experiments.py # Analysis pipeline
│   │   └── utils/                # Lost-success analysis
│   ├── tests/                    # Unit and integration tests
│   ├── requirements.txt
│   └── run_full_experiment.sh    # One-command reproduction
│
├── data/                         # 2,000-lemma dataset and indices
│   ├── input/
│   │   └── synergy_rag_2k.jsonl  # 2,000 lemma drafts (DeepSeek-generated)
│   ├── index/
│   │   ├── coq_lemmas_e5.faiss   # FAISS index (7,200 lemmas, E5 embeddings)
│   │   └── coq_lemmas_e5.pkl     # Metadata
│   └── samples/                  # Small test datasets
│
├── outputs/                      # Experiment results (seed 5)
│   ├── baseline_rag/             # Baseline-RAG results
│   ├── sapse_strict/             # SAPSE-Strict results
│   ├── sapse_fast/               # SAPSE-Fast results
│   ├── sapse_synergy/            # SAPSE-Synergy results
│   ├── analysis/                 # Analysis outputs (Tables 3-6)
│   │   ├── joint_results_2k.csv
│   │   ├── lost_successes.csv    # 96 lost lemmas analysis
│   │   ├── latex/                # Paper tables
│   │   └── lost_casebook.md      # Qualitative examples
│   ├── full_results_seed5.csv    # Combined results (8,000 rows)
│   └── aggregated_results.md     # Summary table
│
├── docs/
│   ├── ARTIFACT.md               # Detailed reproduction guide
│   └── EXPERIMENT_ANALYSIS.md    # Analysis documentation
│
├── LICENSE                       # MIT License
└── README.md                     # This file
```

---

## Reproducing Paper Tables

### Table 2: Overall Results

```bash
cat outputs/aggregated_results.md
```

### Table 3: Per-Category Breakdown

```bash
cat outputs/analysis/latex/category_results.tex
```

### Table 4: Complexity Analysis

```bash
cat outputs/analysis/latex/complexity_results.tex
```

### Table 5: Lost Lemma Failure Modes

```bash
cat outputs/analysis/latex/lost_failure_modes.tex
```

### Table 6 (Appendix): Fragment Coverage

```bash
cat outputs/analysis/latex/fragment_coverage.tex
```

### Qualitative Examples (Section 6.2)

```bash
less outputs/analysis/lost_casebook.md
```

---

## Key Claims and Reproducibility

### Claim 1: Mechanized Soundness (0 Unsafe Rewrites)

**Proof**: All VC passes proven sound in `coq/theories/Sanitizer.v`

```bash
# Verify R_req soundness
grep -A 5 "weakening_req" coq/theories/Sanitizer.v

# Verify R_bind soundness
grep -A 5 "R_bind_typing" coq/theories/Sanitizer.v

# Verify R_eq soundness
grep -A 5 "R_eq_sem" coq/theories/Sanitizer.v

# Verify main soundness theorem
grep -A 10 "Theorem R_AST_sound" coq/theories/Soundness.v
```

**Expected**: All theorems end with `Qed.` (not `Admitted.`)

### Claim 2: Coverage Numbers (37.6% → 32.8%)

```bash
# Count verified lemmas per configuration
grep -c "Baseline-RAG,Verified" outputs/full_results_seed5.csv
# Expected: 752 (37.6%)

grep -c "SAPSE-Fast,Verified" outputs/full_results_seed5.csv
# Expected: 656 (32.8%)

grep -c "SAPSE-Synergy,Verified" outputs/full_results_seed5.csv
# Expected: 656 (32.8%)
```

### Claim 3: Fragment Coverage (98.1%)

```bash
cat outputs/analysis/fragment_coverage_summary.csv
# Expected: in_frag_ratio ≈ 0.981
```

### Claim 4: Lost-Success Analysis (96 Lemmas)

```bash
wc -l outputs/analysis/lost_successes.csv
# Expected: 97 (header + 96 rows)

cat outputs/analysis/lost_successes_summary.json
# Expected: {"total_lost": 96, "failed_in_fast": 96, ...}
```

---

## Testing

### Quick Smoke Test (10 Lemmas)

```bash
cd python/
bash run_full_experiment.sh --limit 10
```

**Expected output**:

- 10 lemmas × 4 configs = 40 rows in `results.csv`
- Aggregated table with ~similar ratios to full experiment
- Completion in ~2-3 minutes

### Full Test Suite

```bash
cd python/
pytest tests/ -v
```

---

## Citation

If you use this artifact in your research, please cite:

```bibtex
@inproceedings{sapse-synergy-fm2026,
  title     = {SAPSE-Synergy: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving},
  author    = {[Author Names]},
  booktitle = {Proceedings of the 26th International Symposium on Formal Methods (FM 2026)},
  year      = {2026},
  doi       = {10.5281/zenodo.XXXXXXX}
}
```

---

## License

This project is licensed under the **MIT License** - see [LICENSE](LICENSE) file for details.

### Third-Party Components

- **CompCert**: INRIA Non-Commercial License (corpus only, not distributed)
- **Coq Standard Library**: LGPL 2.1
- **FAISS**: MIT License
- **Transformers**: Apache 2.0

---

## Support

For questions about artifact evaluation or reproduction:

1. Check [ARTIFACT.md](docs/ARTIFACT.md) for detailed instructions
2. Review [EXPERIMENT_ANALYSIS.md](docs/EXPERIMENT_ANALYSIS.md) for analysis details
3. Open an issue on GitHub (after publication)
4. Contact: [author emails]

---

## Acknowledgments

We thank the FM 2026 artifact evaluation committee and the Coq community for their valuable feedback.

This work was supported by [funding sources].

---

**Status**: ✅ Artifact Complete | Coq Proofs: All Proven (0 Admitted) | Python Tests: Passing

**Last Updated**: 2025-11-08
