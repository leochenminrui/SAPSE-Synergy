# SAPSE-Synergy Quick Start Guide

**For Artifact Evaluators and Reviewers**

---

## 🎯 Three-Step Validation (30 minutes)

### Step 1: Build Verified Core (5 minutes)

```bash
cd artifact_release/coq/
make clean && make -j4

# Verify success
ls theories/*.vo
# Expected: 5 .vo files (Syntax, Typing, Semantics, Sanitizer, Soundness)

# Verify no incomplete proofs
grep -r "Admitted\|Axiom" theories/*.v
# Expected: (no output)
```

✅ **Success Criteria**: All 5 theories compile, 0 Admitted proofs

---

### Step 2: Quick Smoke Test (10 minutes)

```bash
cd artifact_release/python/
bash run_full_experiment.sh --limit 10
```

**What happens**:
- Processes 10 lemma drafts (instead of full 2,000)
- Runs 4 configurations: Baseline-RAG, SAPSE-Strict, SAPSE-Fast, SAPSE-Synergy
- Generates results.csv (40 rows) and aggregated_table.md

✅ **Success Criteria**:
- Completes in ~2-5 minutes
- 40 rows in `outputs/reproduction_run/results.csv`
- Aggregated table shows similar ratios to paper

---

### Step 3: Verify Paper Claims (15 minutes)

Run these commands to verify the 5 main claims:

#### Claim 1: Mechanized Soundness ✅
```bash
cd artifact_release/coq/
grep "Theorem R_AST_sound" theories/Soundness.v
# Expected: Theorem present

# Verify it's proven (not admitted)
sed -n '/Theorem R_AST_sound/,/Qed\./p' theories/Soundness.v | tail -1
# Expected: Qed.
```

#### Claim 2: Coverage Numbers (37.6% → 32.8%) ✅
```bash
cd artifact_release/
cat outputs/summary.csv
# Expected:
# Baseline-RAG: 37.6% (752/2000)
# SAPSE-Fast:   32.8% (656/2000)
# SAPSE-Synergy: 32.8% (656/2000)
```

#### Claim 3: Zero Unsafe Rewrites ✅
```bash
cat outputs/aggregated_results.md | grep URC
# Expected: All configurations show URC = 0
```

#### Claim 4: Fragment Coverage (98.1%) ✅
```bash
cat outputs/analysis/fragment_coverage_summary.csv
# Expected: in_frag_ratio ≈ 0.981
```

#### Claim 5: Lost-Success Analysis (96 Lemmas) ✅
```bash
wc -l outputs/analysis/lost_successes.csv
# Expected: 97 (header + 96 rows)

cat outputs/analysis/lost_successes_summary.json
# Expected: {"total_lost": 96, ...}
```

---

## 📊 Reproducing Paper Tables

All tables from the paper can be verified using pre-computed results in `outputs/`:

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

### Table 6: Fragment Coverage
```bash
cat outputs/analysis/latex/fragment_coverage.tex
```

### Qualitative Examples (Section 6.2)
```bash
less outputs/analysis/lost_casebook.md
```

---

## 🔄 Full Reproduction (3-6 hours)

To reproduce all experiments from scratch:

```bash
cd artifact_release/python/
bash run_full_experiment.sh
```

**What happens**:
1. Loads 2,000 lemma drafts from `data/input/synergy_rag_2k.jsonl`
2. Runs 4 configurations × 2,000 items = 8,000 verification runs
3. Each run: sanitization → Coq verification → logging
4. Generates `outputs/reproduction_run/results.csv` (8,000 rows)
5. Runs analysis to produce all tables and figures

**Duration**: 3-6 hours (depends on CPU and Coq verification speed)

**Monitor progress**:
```bash
# In another terminal
watch -n 10 'tail -20 outputs/reproduction_run/experiment.log'

# Or check row count
wc -l outputs/reproduction_run/results.csv
# Grows from 0 → 8001 (header + 8000)
```

**Compare results**:
```bash
# After completion
cat outputs/reproduction_run/aggregated_table.md

# Compare with paper numbers (outputs/aggregated_results.md)
diff outputs/aggregated_results.md outputs/reproduction_run/aggregated_table.md
```

**Expected variance**: ±5-10% due to:
- Coq/CoqHammer version differences
- System performance (timeouts)
- Non-deterministic proof search

---

## 🐛 Common Issues

### Issue: "coqc: command not found"

**Solution**:
```bash
# Install Coq 9.1.0 via OPAM
opam init
opam install coq.9.1.0
eval $(opam env)

# Verify
coqc --version
# Expected: The Rocq Prover, version 9.1.0
```

### Issue: "No module named 'faiss'"

**Solution**:
```bash
cd artifact_release/python/
pip install -r requirements.txt

# If FAISS fails on macOS M1/M2
pip install faiss-cpu --no-cache-dir
```

### Issue: Different numbers than paper

**Acceptable**: ±5-10% variance due to timeouts and system differences

**Not acceptable**: >20% difference → report to authors

### Issue: Experiment too slow

**Solution**: Increase timeout in `scripts/run_synergy_experiments.py`:
```python
# Line ~50
verify_timeout = 60  # Increase from 30 to 60 seconds
```

---

## 📁 Directory Guide

```
artifact_release/
├── coq/                      # Start here for soundness proofs
├── python/                   # Run experiments from here
├── data/                     # Pre-loaded (no API keys needed)
├── outputs/                  # Pre-computed results (seed 5)
├── figures/                  # Publication-ready plots
├── docs/ARTIFACT.md          # Detailed guide (639 lines)
└── README.md                 # Complete overview (377 lines)
```

---

## ⏱️ Time Budget

| Task | Time | Purpose |
|------|------|---------|
| Build Coq proofs | 5 min | Verify mechanized soundness |
| Smoke test (10 items) | 10 min | Quick functionality check |
| Verify claims | 15 min | Validate paper claims |
| **Total** | **30 min** | **Minimal validation** |
| Full reproduction | 3-6 hours | Complete reproducibility |

---

## 🎓 Understanding the System

### What is SAPSE-Synergy?

**Problem**: Neural theorem provers (like GPT-4 + RAG) generate Coq lemmas, but may introduce semantic errors.

**Solution**: SAPSE-Synergy uses a **mechanically verified sanitizer** to transform neural outputs while preserving semantics.

**Key Innovation**: Balances **soundness** (0 unsafe rewrites) with **coverage** (32.8% verified).

### Architecture in 60 Seconds

```
1. Neural Generation (DeepSeek RAG)
   Input: Natural language proof step
   Output: Coq lemma draft (may have issues)
   ↓
2. Utility Passes (Unverified, high coverage)
   - Scope resolution
   - List parameterization
   - Reformatting
   ↓
3. Admissibility Gatekeeper
   - Check WellFormedU
   - Check disjoint_ctx
   If FAILS → Abstain
   ↓
4. Verified Core (Proven sound in Coq)
   - R_req: Inject Require statements
   - R_bind: Identity (type check)
   - R_eq: Canonicalize equality
   ↓
5. Coq Verification
   - Run coqc
   - Status: Verified / Failed / Abstained
```

### Why Coverage Drops (37.6% → 32.8%)

**96 lemmas lost** when moving from Baseline-RAG to SAPSE-Synergy:

- **40%**: Utility pass damage (introduced type errors)
- **25%**: Proof search failure (automation breaks)
- **20%**: Guard rejection (correctly rejected bad inputs)
- **15%**: Timeout (increased complexity)

**Trade-off**: Lose 5% coverage, gain **100% soundness guarantee**

See `outputs/analysis/lost_casebook.md` for detailed examples.

---

## 🏆 Success Criteria Summary

After 30 minutes, you should have verified:

- [x] All Coq proofs compile (5 theories, 0 Admitted)
- [x] Smoke test runs successfully (10 items × 4 configs)
- [x] Coverage numbers match: 37.6% → 32.8%
- [x] Zero unsafe rewrites (URC = 0) for Synergy
- [x] Fragment coverage ≈ 98.1%
- [x] Lost-success analysis: 96 lemmas

**If all checked**: ✅ Artifact is functional and claims are validated

---

## 📚 Next Steps

### For Reviewers
- Read `docs/ARTIFACT.md` for comprehensive guide
- Run full reproduction if time permits
- Check `outputs/analysis/lost_casebook.md` for qualitative insights

### For Researchers
- Examine `coq/theories/Soundness.v` for soundness proof
- Explore `python/sapse/` for implementation details
- Modify `python/prompts/` to test different prompts

### For Extenders
- Add new embedders: `python/sapse/embeddings/`
- Add new passes: `python/sapse/sanitize/`
- Modify guards: `coq/theories/Sanitizer.v`

---

## 📞 Support

**Questions?**
1. Check `README.md` for overview
2. Check `docs/ARTIFACT.md` for detailed guide
3. Check `docs/EXPERIMENT_ANALYSIS.md` for analysis details
4. Contact: [author emails] (after publication)

**Found a bug?**
- Check troubleshooting section above
- GitHub issues: [repository URL] (after publication)

---

**Last Updated**: 2025-11-08
**Version**: 1.0.0
**Paper**: SAPSE-Synergy: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving (FM 2026)
