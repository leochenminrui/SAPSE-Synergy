# Why `data/corpora/` is Empty - Quick Explanation

## TL;DR

**The `data/corpora/` directory is intentionally empty.** This is correct and by design.

All necessary data is **pre-processed and included** in:
- ✅ `data/index/coq_lemmas_e5.faiss` (21 MB) - FAISS index
- ✅ `data/index/coq_lemmas_e5.pkl` (3.8 MB) - Metadata
- ✅ `data/input/synergy_rag_2k.jsonl` (2.1 MB) - Experiment input

**No additional downloads required** for artifact evaluation.

---

## Three Reasons

### 1. **Licensing**
CompCert has a non-commercial license that prohibits redistribution. We include only the derived data (lemma text and embeddings), which is permitted for research.

### 2. **Size**
Raw corpora would add ~650 MB (CompCert 500 MB + Coq-stdlib 100 MB + Coq-ext-lib 50 MB). The pre-processed data is only ~27 MB.

### 3. **Not Needed**
For artifact evaluation, reviewers need to:
- ✅ Run experiments on 2,000 lemmas
- ✅ Verify results match paper numbers
- ❌ NOT rebuild FAISS index from scratch

---

## What's Included Instead

Instead of raw `.v` files, we provide:

| File | Size | Purpose | Status |
|------|------|---------|--------|
| `coq_lemmas_e5.faiss` | 21 MB | Vector index for 7,200 lemmas | ✅ Ready |
| `coq_lemmas_e5.pkl` | 3.8 MB | Lemma text and metadata | ✅ Ready |
| `synergy_rag_2k.jsonl` | 2.1 MB | 2,000 experiment inputs | ✅ Ready |

**All experiments run directly from these files.**

---

## Verification

To verify the data is complete and valid:

```bash
# Check FAISS index exists
ls -lh data/index/coq_lemmas_e5.faiss
# Expected: 21 MB

# Check metadata exists
ls -lh data/index/coq_lemmas_e5.pkl
# Expected: 3.8 MB

# Count lemmas in index
python3 -c "import pickle; print(len(pickle.load(open('data/index/coq_lemmas_e5.pkl', 'rb'))))"
# Expected: 7200

# Check input dataset
wc -l data/input/synergy_rag_2k.jsonl
# Expected: 2000
```

All checks pass ✅

---

## For More Details

- **Full explanation**: See `DATA_DESIGN.md`
- **Corpora README**: See `data/corpora/README.md`
- **Licensing info**: See `LICENSE`

---

## Bottom Line

**Empty `corpora/` = Correct ✅**

The artifact is **self-contained** and **fully functional** without raw corpora.

No action required from evaluators.

---

**Last Updated**: 2025-11-08
