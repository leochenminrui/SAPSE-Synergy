# SAPSE-Synergy Experiment Recon Summary

**Date**: 2025-11-08
**Author**: Claude (Code Assistant)

## Task 0: Reconnaissance Findings

### 1. Main 2K Experiment Script

**Primary Script**: `scripts/run_synergy_experiments.py`

This script runs all 4 configurations (Baseline-RAG, SAPSE-Strict, SAPSE-Fast, SAPSE-Synergy) on the 2K dataset.

**Usage**:
```bash
python scripts/run_synergy_experiments.py \
  --input data/synergy_rag_2k.jsonl \
  --output-dir outputs/synergy_deepseek_real_2k_seed5
```

### 2. Four Configuration Definitions

**Location**: `sapse/sanitize/pipelines.py`

The four pipelines are defined as follows:

1. **Baseline-RAG**:
   - No sanitization passes
   - Direct RAG output → Coq verification
   - Purpose: Establishes baseline performance

2. **SAPSE-Strict** (VC-only):
   - Pre-gatekeeper: `check_admissible_spec()`
   - If admissible → Apply Passes 1-3 (verified core: R_req, R_bind, R_eq)
   - If not admissible → Abstain
   - Purpose: Demonstrates verified transformations only (safety-first)

3. **SAPSE-Fast** (UP-only):
   - Apply Passes 1, 3, 4, 5, 6 (P1: R_req, P3: R_eq, P4-6: unverified utility)
   - No admissibility gatekeeper
   - URC detection for unsafe rewrites
   - Purpose: Shows coverage without safety guarantees

4. **SAPSE-Synergy** (UP + VC):
   - Pre-process with UP passes 4-6 (scope, list, reformat)
   - Check `admissible_spec()` on pre-processed AST
   - If admissible → Apply VC passes 1-3
   - If not admissible → Abstain
   - Purpose: Synergy hypothesis - UP preprocessing + VC gatekeeper

### 3. Per-Sample Log Format

**Primary Log**: `outputs/synergy_deepseek_real_2k_seed*/results.csv`

**CSV Schema**:
```
item_id,config_name,status,time_ms,urc_flag
```

**Example**:
```csv
CompCert:Stacklayout:frame_env_separated,Baseline-RAG,Failed,452.77,0
CompCert:Stacklayout:frame_env_separated,SAPSE-Strict,Abstained,12.34,0
CompCert:Stacklayout:frame_env_separated,SAPSE-Fast,Verified,234.56,0
CompCert:Stacklayout:frame_env_separated,SAPSE-Synergy,Abstained,156.78,0
```

**Fields**:
- `item_id`: Unique lemma identifier (format: `CompCert:Module:lemma_name`)
- `config_name`: One of {Baseline-RAG, SAPSE-Strict, SAPSE-Fast, SAPSE-Synergy}
- `status`: One of {Verified, Failed, Abstained, Error}
- `time_ms`: Verification time in milliseconds
- `urc_flag`: Unsafe rewrite count (0 or 1)

**Auxiliary Logs**:
- `error_traces.jsonl`: Per-lemma error messages and traces (optional)
- `experiment.log`: Full runtime log
- `aggregated_table.md`: Summary table with overall stats

### 4. Input Data Format

**File**: `data/synergy_rag_2k.jsonl`
**Size**: 2.1 MB
**Entries**: 2,000 lemmas (one per line)

**JSON Schema** (per line):
```json
{
  "id": "CompCert:Stacklayout:frame_env_separated",
  "draft": "Lemma ... Qed.",
  "nl_proof": "Step 1: ... Step 2: ...",
  "retrieved_count": 0,
  "metadata": {
    "source": "data/nl_steps/all_proofs_grouped.jsonl",
    "top_k": 10,
    "threshold": 0.8
  }
}
```

**Key Fields**:
- `id`: Lemma identifier (stable, unique)
- `draft`: Generated Coq lemma from DeepSeek RAG
- `nl_proof`: Natural language proof steps (for reference)
- `metadata`: RAG generation metadata

### 5. Verified Numbers

**Experiment**: `outputs/synergy_deepseek_real_2k_seed5`

**Verified Counts** (from results.csv):
- **Baseline-RAG**: 752 / 2000 = 37.6%
- **SAPSE-Strict**: (to be counted)
- **SAPSE-Fast**: 656 / 2000 = 32.8%
- **SAPSE-Synergy**: 656 / 2000 = 32.8%

**Lost Successes**: 752 - 656 = **96 lemmas**

These are lemmas verified by Baseline-RAG but NOT verified by Fast/Synergy.

### 6. Existing Analysis Infrastructure

**Script**: `scripts/analyze_synergy_experiments.py`

**Already Implemented** (as of 2025-11-08):
- ✅ Task 7: Joint per-lemma results table (`build_joint_results_table()`)
- ✅ Task 1: Fragment coverage analysis (`analyze_fragment_coverage()`)
- ✅ Task 2: Semantic category breakdown (`analyze_categories()`)
- ✅ Task 3: Structural complexity analysis (`analyze_complexity()`)
- ⚠️ Task 4: Core vs Fast (stub only)
- ⚠️ Task 5: Extra baselines (stub only)
- ⚠️ Task 8-13: Lost-success analysis (placeholder module import)

**Data Structures**:
- `LemmaRecord`: Unified per-lemma record with all configurations
- `CategoryStats`: Per-category aggregated statistics
- `FragmentCoverageStats`: Fragment coverage statistics
- `ComplexityStats`: Complexity band statistics

### 7. Current Output Structure

**Analysis Outputs**: `outputs/analysis/`

**Generated Files**:
- `joint_results_2k.csv`: Master table with all configurations aligned
- `fragment_coverage_summary.csv`: Fragment coverage stats
- `category_results.csv`: Per-category breakdown
- `complexity_results.csv`: Per-complexity-band breakdown
- `latex/fragment_coverage.tex`: LaTeX table for fragment coverage
- `latex/category_results.tex`: LaTeX table for categories
- `latex/complexity_results.tex`: LaTeX table for complexity

### 8. Dependencies and Imports

**Key Modules**:
- `sapse/sanitize/passes.py`: Pass definitions (1-6) and AdmissibleSpec
- `sapse/sanitize/pipelines.py`: Four pipeline implementations
- `sapse/verify/coq_verify.py`: Real Coq verification
- `scripts/run_synergy_experiments.py`: Main experiment runner
- `scripts/analyze_synergy_experiments.py`: Main analysis script

**External Libraries**:
- `loguru`: Logging
- `dataclasses`: Data structures
- `csv`, `json`, `yaml`: Data I/O
- `re`: Pattern matching
- `pathlib`: Path handling

### 9. Key Invariants (DO NOT BREAK)

**Experimental Semantics**:
1. The four configurations have fixed semantics (defined in pipelines.py)
2. Input data (`synergy_rag_2k.jsonl`) is immutable
3. Results CSV format is stable (5 columns)
4. Lemma IDs are deterministic and stable across runs

**Analysis Constraints**:
1. All analyses are **read-only** - they do not modify experiments
2. Joint table alignment uses `item_id` as the stable key
3. Categories, complexity, and fragment coverage are **deterministic annotations**
4. Lost-success analysis compares Baseline-RAG vs Fast/Synergy statuses

### 10. Next Steps

**PART I - Extended Analysis** (Tasks 1-6):
- ✅ Fragment coverage (mostly done, needs per-category breakdown)
- ✅ Semantic categories (done)
- ✅ Structural complexity (done)
- ⚠️ Core vs Fast comparison (needs rewrite instrumentation)
- ⚠️ Extra baselines (needs new experiment runs)

**PART II - Lost-Success Differential** (Tasks 8-13):
- ⚠️ Isolate 96 lost lemmas
- ⚠️ Compare original vs sanitized statements
- ⚠️ Failure mode breakdown
- ⚠️ Category/complexity of lost lemmas
- ⚠️ Build lost lemma casebook

**Integration**:
- Update `analyze_synergy_experiments.py` with missing tasks
- Create `docs/EXPERIMENT_ANALYSIS.md` documentation
- Add utility module for lost-success analysis

---

## Summary

The SAPSE-Synergy experiment infrastructure is **well-established** with a clean separation between:

1. **Experiment execution** (`run_synergy_experiments.py`)
2. **Data logging** (results.csv, error_traces.jsonl)
3. **Analysis** (`analyze_synergy_experiments.py`)

The existing analysis script has **solid foundations** for Tasks 1-3 (fragment, category, complexity).

**What needs to be built**:
- Task 4: Instrumentation for UP rewrite tracking (requires modifying passes.py)
- Task 5: New baseline experiments (regex sanitizer, CoqHammer-only)
- Tasks 8-13: Complete lost-success differential analysis module

**Key Finding**: The experiment semantics are **preserved** and analysis is **additive**. No risk of breaking existing functionality.
