# SAPSE-Synergy Pre-Release Checklist

**Use this checklist before submitting the artifact for evaluation**

---

## ✅ Critical Items (Must Complete)

### Documentation Updates

- [ ] **README.md:3** - Update Zenodo DOI badge
  ```markdown
  Current: [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)]
  Update to: [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.ACTUAL_ID.svg)]
  ```

- [ ] **README.md:332** - Update citation author names
  ```bibtex
  Current: author    = {[Author Names]},
  Update to: author    = {First Author and Second Author and Third Author},
  ```

- [ ] **README.md:336** - Update citation DOI
  ```bibtex
  Current: doi       = {10.5281/zenodo.XXXXXXX}
  Update to: doi       = {10.5281/zenodo.ACTUAL_ID}
  ```

- [ ] **README.md:362** - Update contact email
  ```markdown
  Current: 4. Contact: [author emails]
  Update to: 4. Contact: first.author@university.edu, second.author@university.edu
  ```

- [ ] **ARTIFACT.md:627** - Update citation author names
  ```bibtex
  Current: author    = {[Author Names]},
  Update to: author    = {First Author and Second Author and Third Author},
  ```

- [ ] **ARTIFACT.md:630** - Update citation DOI
  ```bibtex
  Current: doi       = {10.5281/zenodo.XXXXXXX}
  Update to: doi       = {10.5281/zenodo.ACTUAL_ID}
  ```

- [ ] **ARTIFACT.md:615** - Update GitHub repository URL
  ```markdown
  Current: - GitHub issues: [repository URL]
  Update to: - GitHub issues: https://github.com/username/sapse-synergy/issues
  ```

- [ ] **ARTIFACT.md:616** - Update contact email
  ```markdown
  Current: - Email: [author emails]
  Update to: - Email: first.author@university.edu
  ```

- [ ] **QUICKSTART.md** - Update contact placeholders (bottom of file)
  ```markdown
  Current: Contact: [author emails] (after publication)
  Update to: Contact: first.author@university.edu

  Current: GitHub issues: [repository URL] (after publication)
  Update to: GitHub issues: https://github.com/username/sapse-synergy/issues
  ```

### Zenodo Preparation

- [ ] Create Zenodo deposit
- [ ] Upload artifact_release/ directory (zip or tar.gz)
- [ ] Add metadata:
  - Title: "SAPSE-Synergy: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving (Artifact)"
  - Authors: [List all authors with affiliations and ORCIDs]
  - Description: Use README.md overview section
  - Keywords: theorem proving, formal verification, Coq, neural networks, RAG, sanitization
  - License: MIT
  - Related publication: FM 2026 paper DOI
- [ ] Publish and get DOI
- [ ] Update all references to Zenodo DOI in documentation

---

## ✅ Validation Tests (Run Before Release)

### 1. Clean Build Test
```bash
cd artifact_release/coq/
make clean
make -j4
# Expected: All 5 theories compile, no errors

grep -r "Admitted\|Axiom" theories/*.v
# Expected: No output (all proofs complete)
```

- [ ] Coq proofs build successfully
- [ ] No Admitted or Axiom statements
- [ ] Build completes in <5 minutes

### 2. Smoke Test
```bash
cd artifact_release/python/
bash run_full_experiment.sh --limit 10
# Expected: Completes in 2-5 minutes, 40 rows in results.csv
```

- [ ] Smoke test completes successfully
- [ ] 40 rows generated (10 items × 4 configs)
- [ ] Aggregated table shows reasonable ratios

### 3. Data Integrity
```bash
wc -l artifact_release/data/input/synergy_rag_2k.jsonl
# Expected: 2000

ls -lh artifact_release/data/index/
# Expected: coq_lemmas_e5.faiss (~21 MB), coq_lemmas_e5.pkl (~3.8 MB)
```

- [ ] Dataset has exactly 2,000 lines
- [ ] FAISS index present and correct size
- [ ] Metadata pickle present

### 4. Results Verification
```bash
cat artifact_release/outputs/summary.csv
# Expected: Baseline-RAG: 752/2000 (37.6%), Synergy: 656/2000 (32.8%)

wc -l artifact_release/outputs/full_results_seed5.csv
# Expected: 8001 (header + 8000)

wc -l artifact_release/outputs/analysis/lost_successes.csv
# Expected: 97 (header + 96)
```

- [ ] Summary CSV matches paper numbers
- [ ] Full results has 8,000 data rows
- [ ] Lost-success analysis has 96 lemmas

### 5. Documentation Check
```bash
# Check all markdown files render correctly
ls artifact_release/*.md
ls artifact_release/docs/*.md

# Verify no broken links (manual review)
grep -r "XXXXXXX" artifact_release/*.md artifact_release/docs/*.md
# Expected: No matches after updating DOIs
```

- [ ] All markdown files present
- [ ] No placeholder text (XXXXXXX, [Author Names], etc.)
- [ ] No broken links or references

---

## ✅ Repository Structure Verification

### Required Files
- [ ] `coq/` directory with 5 .v files
- [ ] `python/` directory with sapse/, scripts/, tests/, requirements.txt
- [ ] `data/input/synergy_rag_2k.jsonl` (2,000 lines)
- [ ] `data/index/coq_lemmas_e5.faiss` and `.pkl`
- [ ] `outputs/` with baseline_rag/, sapse_strict/, sapse_fast/, sapse_synergy/
- [ ] `outputs/analysis/` with all CSV and LaTeX files
- [ ] `figures/` with all PDF and PNG files
- [ ] `README.md` (top-level overview)
- [ ] `docs/ARTIFACT.md` (evaluation guide)
- [ ] `docs/EXPERIMENT_ANALYSIS.md` (analysis docs)
- [ ] `QUICKSTART.md` (30-min guide)
- [ ] `RELEASE_VALIDATION.md` (validation report)
- [ ] `LICENSE` (MIT)
- [ ] `.gitignore` (configured to include essential files)

### File Size Check
```bash
du -sh artifact_release/
# Expected: ~35 MB total

du -sh artifact_release/data/index/
# Expected: ~25 MB (FAISS + metadata)

du -sh artifact_release/outputs/
# Expected: ~1-2 MB (CSVs and markdown)
```

- [ ] Total size <100 MB (suitable for Zenodo free tier)
- [ ] No unnecessarily large files
- [ ] FAISS index present and not gitignored

---

## ✅ Final Quality Checks

### Code Quality
- [ ] All Python files have docstrings
- [ ] All Coq files have comments
- [ ] No hardcoded paths (all relative)
- [ ] No API keys in code (use environment variables)

### Documentation Quality
- [ ] All commands in docs have expected outputs
- [ ] All error messages have troubleshooting guidance
- [ ] All placeholders updated
- [ ] Consistent terminology throughout

### User Experience
- [ ] Clear quick-start path (QUICKSTART.md)
- [ ] Clear troubleshooting section (ARTIFACT.md)
- [ ] Clear time estimates for all tasks
- [ ] Clear success criteria for all validations

---

## ✅ Git Repository Preparation (If Using Git)

### .gitignore Configuration
```bash
cat artifact_release/.gitignore | grep -A 3 "Large files"
# Expected: Includes exceptions for data/index/*.faiss and data/index/*.pkl
```

- [ ] .gitignore allows essential FAISS files
- [ ] .gitignore excludes temporary files (.vo, .vok, etc.)
- [ ] .gitignore excludes Python cache (__pycache__, *.pyc)

### Git LFS (If Files >50 MB)
If any file exceeds 50 MB (check with `find artifact_release -size +50M`):

- [ ] Install Git LFS: `git lfs install`
- [ ] Track large files: `git lfs track "*.faiss"`
- [ ] Commit .gitattributes
- [ ] Verify tracking: `git lfs ls-files`

### Initial Commit
```bash
cd artifact_release/
git init
git add .
git commit -m "Initial release: SAPSE-Synergy artifact for FM 2026"
git tag v1.0.0
```

- [ ] Repository initialized
- [ ] All files committed
- [ ] Version tagged (v1.0.0)

---

## ✅ Zenodo Upload Checklist

### Preparation
- [ ] Create archive: `tar -czf sapse-synergy-artifact-v1.0.0.tar.gz artifact_release/`
- [ ] Verify archive: `tar -tzf sapse-synergy-artifact-v1.0.0.tar.gz | head -20`
- [ ] Test extraction: `tar -xzf sapse-synergy-artifact-v1.0.0.tar.gz -C /tmp/`

### Zenodo Metadata
- [ ] **Title**: SAPSE-Synergy: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving (Artifact)
- [ ] **Upload type**: Dataset (or Software)
- [ ] **Publication date**: [FM 2026 acceptance date]
- [ ] **DOI**: Reserve DOI before publishing
- [ ] **Authors**: All authors with affiliations and ORCIDs
- [ ] **Description**:
  ```
  This artifact accompanies the FM 2026 paper "SAPSE-Synergy: Balancing Formal Soundness
  and Empirical Coverage in Neural Theorem Proving."

  It includes:
  - Mechanically verified AST sanitizer (Rocq 9.1.0, 0 Admitted proofs)
  - Complete Python pipeline for retrieval + sanitization + verification
  - 2,000-lemma dataset with pre-computed FAISS index
  - Full experimental results (4 configurations × 2,000 items)
  - All tables and figures from the paper
  - Comprehensive documentation (>2,500 lines)

  Quick start: See QUICKSTART.md for 30-minute validation.
  Full guide: See docs/ARTIFACT.md for detailed instructions.
  ```
- [ ] **Keywords**: theorem proving, formal verification, Coq, Rocq, neural networks, RAG, sanitization, soundness
- [ ] **License**: MIT
- [ ] **Communities**: Formal Methods, Programming Languages, Artificial Intelligence
- [ ] **Related identifiers**: FM 2026 paper DOI (if available)
- [ ] **Version**: 1.0.0
- [ ] **Language**: English

### Pre-Publication Check
- [ ] Preview deposit
- [ ] Verify all metadata correct
- [ ] Verify archive downloads correctly
- [ ] Verify archive size (<50 GB for Zenodo free tier)

### Publication
- [ ] Publish deposit
- [ ] Copy DOI (format: 10.5281/zenodo.XXXXXXX)
- [ ] Update all documentation with actual DOI
- [ ] Verify DOI badge works in README.md

---

## ✅ Submission Checklist

### For Artifact Evaluation Committee
- [ ] Upload artifact archive to Zenodo
- [ ] Get Zenodo DOI badge
- [ ] Update all documentation with DOI
- [ ] Submit Zenodo link to artifact evaluation system
- [ ] Include QUICKSTART.md in submission form as "getting started" guide
- [ ] Include estimated evaluation time: 30 min (quick), 4-7 hours (full)

### For Camera-Ready Version
- [ ] Update paper with Zenodo DOI reference
- [ ] Add artifact badge to paper (if awarded)
- [ ] Update acknowledgments (if needed)

---

## ✅ Post-Release Checklist

### Immediate (Day 1)
- [ ] Verify Zenodo DOI works
- [ ] Verify download from Zenodo works
- [ ] Test fresh extraction and quick validation
- [ ] Monitor artifact evaluation feedback

### Short-term (Week 1)
- [ ] Respond to evaluator questions
- [ ] Fix any critical issues found
- [ ] Prepare v1.0.1 if needed

### Long-term (Month 1)
- [ ] Create GitHub repository (after paper acceptance)
- [ ] Add CI/CD for automated testing
- [ ] Monitor community usage
- [ ] Consider Docker image for easier reproduction

---

## ✅ Optional Enhancements (Not Required)

### GitHub Repository (Post-Acceptance)
- [ ] Create public repository
- [ ] Add GitHub Actions for CI/CD
- [ ] Add CITATION.cff for GitHub citation
- [ ] Add badges: DOI, License, Build Status
- [ ] Add CONTRIBUTING.md
- [ ] Add CODE_OF_CONDUCT.md

### Docker Image
- [ ] Create Dockerfile with Coq 9.1.0 + Python 3.10
- [ ] Pre-install all dependencies
- [ ] Test one-command execution in Docker
- [ ] Push to Docker Hub
- [ ] Update documentation with Docker instructions

### Video Walkthrough
- [ ] Record 5-min quick start video
- [ ] Record 15-min full walkthrough
- [ ] Upload to YouTube or Vimeo
- [ ] Add link to README.md

---

## 📋 Quick Pre-Flight Check

Run these 5 commands before submission:

```bash
# 1. Clean build
cd artifact_release/coq/ && make clean && make -j4

# 2. No admitted
grep -r "Admitted\|Axiom" artifact_release/coq/theories/*.v

# 3. Smoke test
cd artifact_release/python/ && bash run_full_experiment.sh --limit 10

# 4. Data integrity
wc -l artifact_release/data/input/synergy_rag_2k.jsonl

# 5. No placeholders
grep -r "XXXXXXX\|\[Author Names\]\|\[author emails\]" artifact_release/*.md artifact_release/docs/*.md
```

**All 5 must pass** before submission.

---

## 🎯 Timeline Recommendation

| Task | Duration | When |
|------|----------|------|
| Update placeholders | 30 min | Day -3 |
| Run validation tests | 1 hour | Day -3 |
| Create Zenodo deposit | 30 min | Day -2 |
| Upload and verify | 1 hour | Day -2 |
| Get DOI and update docs | 30 min | Day -1 |
| Final review | 1 hour | Day -1 |
| Submit to AE | 15 min | Day 0 |

**Total**: ~5 hours spread over 3 days

---

## ✅ Sign-Off

Before submitting, verify:

- [ ] All critical items completed
- [ ] All validation tests passed
- [ ] All placeholders updated
- [ ] Zenodo DOI obtained and integrated
- [ ] Documentation reviewed and polished
- [ ] Quick pre-flight check passed (all 5 commands)

**Ready for submission**: ✅ / ⬜

**Submitted by**: _________________ **Date**: _________________

---

**Last Updated**: 2025-11-08
**Artifact Version**: 1.0.0
**Target**: FM 2026 Artifact Evaluation
