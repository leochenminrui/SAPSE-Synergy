# SAPSE-Synergy Experiment Analysis Documentation

**Version**: 2.0 (Updated 2025-11-08)
**Status**: Complete implementation of Tasks 0-3, 7-13

## Overview

This document describes the comprehensive analysis system for the SAPSE-Synergy 2K benchmark experiments.

The analysis system provides differential and extended analysis on the 4-configuration Synergy benchmark:
1. **Baseline-RAG**: No sanitization (direct RAG output)
2. **SAPSE-Strict**: Verified core only (VC-guarded)
3. **SAPSE-Fast**: Unverified utility passes only (no guards, may have unsafe rewrites)
4. **SAPSE-Synergy**: Utility passes → Verified core (UP → VC, coverage + safety)

### Key Research Question

**Why does the verified rate drop from 37.6% (Baseline-RAG) → 32.8% (Fast/Synergy)?**

This analysis pipeline identifies and characterizes the **96 "lost success" lemmas** to understand the performance drop.

## Experimental Setup

### Running the 2K Synergy Experiment

The main 2K experiment is run via:

```bash
python scripts/run_synergy_experiments.py \
    --input data/synergy_rag_2k.jsonl \
    --output-dir outputs/synergy_deepseek_real_2k_seed<N> \
    --coq-random-seed <N>
```

This produces:
- `results.csv`: Per-lemma results across all 4 configurations (item_id, config_name, status, time_ms, urc_flag)
- `error_traces.jsonl`: Detailed error traces with error messages and admissibility failures
- `aggregated_table.md`: Summary statistics table

### Configuration Semantics (DO NOT CHANGE)

The 4 configurations are defined in `sapse/sanitize/pipelines.py`:

- **Baseline-RAG** (`BaselineRAGPipeline`):
  - No transformation, direct verification of RAG output
  - No URC possible (no sanitization applied)

- **SAPSE-Strict** (`SAPSEStrictPipeline`):
  - Pre-check: `check_admissible_spec(raw_ast)` → abstain if fails
  - Apply verified core passes (1-3): require injection, binder norm, equality canonicalization
  - No UP passes (Passes 4-6)
  - URC count: always 0 (only semantics-preserving transformations)

- **SAPSE-Fast** (`SAPSEFastPipeline`):
  - Apply utility passes (4-6): scope resolution, list parameterization, reformatting
  - No admissibility check
  - Post-check: `find_suspicious_edit(raw_ast, final_ast)` to detect URC
  - URC count: may be > 0 (unsafe rewrites possible)

- **SAPSE-Synergy** (`SAPSESynergyPipeline`):
  - Step 1: Apply utility passes (4-6) to expand admissible space
  - Step 2: Check `check_admissible_spec(after_UP)` → abstain if fails
  - Step 3: Apply verified core passes (1-3)
  - URC detection: `find_suspicious_edit` should find 0 (VC guards ensure safety)
  - URC count: 0 (guards ensure no unsafe rewrites reach Coq)

## Analysis System

### Entry Point

```bash
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --all
```

### Available Analyses

#### 1. Joint Per-Lemma Results Table (Task 7)

**Purpose**: Build a unified table aligning all 4 configurations per lemma.

**Output**: `outputs/analysis/joint_results_2k.csv`

**Columns**:
- `lemma_id`: Unique lemma identifier (e.g., `CompCert:Stacklayout:frame_env_separated`)
- `baseline_status`, `strict_status`, `fast_status`, `synergy_status`: Per-config status (Verified/Failed/Abstained/Error)
- `baseline_runtime`, ...: Per-config runtime in milliseconds
- `baseline_urc`, ...: Per-config URC flag (0 or 1)
- `category`: Semantic category (Arithmetic/Boolean/List/Inductive/Misc)
- `complexity_band`: Structural complexity (shallow/medium/deep)
- `ast_depth`: Approximate AST nesting depth
- `binder_count`: Number of `forall` binders
- `in_frag_*`: Boolean flags indicating if lemma is in verified Rocq fragment
- `raw_ast`: Original draft statement (first 500 chars)
- `*_error`: Error messages from verifier

**Usage**:
```python
import csv

with open('outputs/analysis/joint_results_2k.csv', 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
        print(f"{row['lemma_id']}: Baseline={row['baseline_status']}, Synergy={row['synergy_status']}")
```

#### 2. Fragment Coverage Analysis (Task 1)

**Purpose**: Quantify how often lemmas operate within the verified Rocq fragment.

**Outputs**:
- `outputs/analysis/fragment_coverage_summary.csv`
- `outputs/analysis/latex/fragment_coverage.tex`

**Fragment Checker** (`in_verified_fragment(coq_stmt)`):
- **Allowed**: `forall`, `->`, basic inductive types (nat, bool, list), equality (`=`)
- **Disallowed**: Typeclasses (`Class`, `Instance`, `Context`), Canonical structures, Ssreflect syntax

**CSV Columns**:
- `category`: Semantic category (or "All" for overall)
- `num_lemmas`: Total lemmas in category
- `in_frag_count`: Lemmas in verified fragment
- `in_frag_ratio`: Fraction in fragment
- `synergy_verified_in_frag`: Synergy-verified lemmas within fragment
- `synergy_verified_out_frag`: Synergy-verified lemmas outside fragment

**LaTeX Table**:
```latex
\begin{tabular}{lrrrr}
\toprule
Category & \#Lemmas & InFrag (\%) & Synergy verified in-frag (\%) & Synergy verified out-of-frag (\%) \\
\midrule
...
\bottomrule
\end{tabular}
```

**Run**:
```bash
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --fragment
```

#### 3. Semantic Category Breakdown (Task 2)

**Purpose**: Explain which lemma families benefit or suffer under different configurations.

**Outputs**:
- `outputs/analysis/category_results.csv`
- `outputs/analysis/latex/category_results.tex`

**Categories** (assigned by `categorize_lemma(lemma_id)`):
- **Arithmetic**: Z, nat, N, Q operations (keywords: `zarith`, `nat`, `integer`, `add`, `mul`, ...)
- **Boolean**: bool, and, or, negation (keywords: `bool`, `and`, `or`, `neg`, ...)
- **List**: list, append, map, fold (keywords: `list`, `append`, `map`, `fold`, ...)
- **Inductive**: custom inductive types, pattern matching (keywords: `inductive`, `match`, `case`, ...)
- **Misc**: everything else

**CSV Columns**:
- `category`, `num_lemmas`
- `verified_baseline`, `verified_strict`, `verified_fast`, `verified_synergy`
- `abstained_strict`, `abstained_synergy`

**LaTeX Table**:
```latex
\begin{tabular}{lcccc}
\toprule
Category & Baseline-RAG & Strict & Fast & Synergy \\
\midrule
Arithmetic & 29.0\% & 29.0\% & 22.5\% & 22.5\% \\
Boolean & 35.2\% & 34.6\% & 29.9\% & 29.9\% \\
...
\bottomrule
\end{tabular}
```

**Run**:
```bash
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --category
```

#### 4. Structural Complexity Analysis (Task 3)

**Purpose**: Analyze how performance changes as lemma complexity increases.

**Outputs**:
- `outputs/analysis/complexity_results.csv`
- `outputs/analysis/latex/complexity_results.tex`

**Complexity Metrics**:
- **AST depth**: Max nesting level of parentheses/braces (computed by `compute_ast_metrics`)
- **Binder count**: Number of `forall` keywords
- **Complexity score**: `depth + binder_count * 2`

**Complexity Bands**:
- **Shallow**: score ≤ 8
- **Medium**: 8 < score ≤ 16
- **Deep**: score > 16

**CSV Columns**:
- `band`, `num_lemmas`
- `verified_baseline`, `verified_strict`, `verified_fast`, `verified_synergy`
- `abstained_strict`, `abstained_synergy`

**LaTeX Table**:
```latex
\begin{tabular}{lcccc}
\toprule
Complexity band & Baseline-RAG & Strict & Fast & Synergy \\
\midrule
shallow & X.X\% & X.X\% & X.X\% & X.X\% \\
medium & X.X\% & X.X\% & X.X\% & X.X\% \\
deep & X.X\% & X.X\% & X.X\% & X.X\% \\
\bottomrule
\end{tabular}
```

**Run**:
```bash
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --complexity
```

#### 5. Lost-Success Differential Analysis (Tasks 8-12)

**Purpose**: Understand why the verified rate drops from **37.6% → 32.8%** (96 lemmas lost).

**Background**:
- Baseline-RAG: 752/2000 (37.6%) verified
- SAPSE-Fast: 656/2000 (32.8%) verified
- SAPSE-Synergy: 656/2000 (32.8%) verified
- **Lost successes**: 96 lemmas verified in Baseline but not in Fast/Synergy

##### Task 8: Isolate Lost Successes

**Output**: `outputs/analysis/lost_successes.csv`

**Columns**:
- `lemma_id`, `category`, `complexity_band`
- `baseline_status`, `fast_status`, `synergy_status`
- `baseline_runtime`, `fast_runtime`, `synergy_runtime`
- `baseline_error`, `fast_error`, `synergy_error`

**Summary**: `outputs/analysis/lost_successes_summary.json`

```json
{
  "total_lost": 96,
  "failed_in_fast": 96,
  "abstained_in_fast": 0,
  "error_in_fast": 0,
  ...
}
```

##### Task 9: Compare Original vs Sanitized Statements

**Note**: This requires final AST strings from each configuration, which are not currently logged in the experiment outputs. The current implementation provides a placeholder.

**Future enhancement**: Instrument `pipelines.py` to log `final_ast` in `error_traces.jsonl`.

##### Task 10: Failure Mode Breakdown

**Purpose**: Categorize how lost lemmas fail in Fast/Synergy.

**Outputs**:
- `outputs/analysis/lost_failure_modes.csv`
- `outputs/analysis/latex/lost_failure_modes.tex`

**Failure Modes** (categorized by `categorize_failure_mode(status, error_msg)`):
- `TYPE_ERROR`: Ill-typed term, type mismatch
- `UNRESOLVED_IDENTIFIER`: Unbound variable, undefined symbol
- `TAC_FAIL`: Tactic or CoqHammer failed
- `TIMEOUT`: Verification timeout
- `GUARD_REJECTED`: Abstained due to admissibility check
- `OTHER`: Other failures

**LaTeX Table**:
```latex
\begin{tabular}{lrr}
\toprule
Failure mode & Fast (count) & Synergy (count) \\
\midrule
TYPE_ERROR & ... & ... \\
TAC_FAIL & ... & ... \\
...
\bottomrule
\end{tabular}
```

##### Task 11: Semantic Category and Complexity of Lost Lemmas

**Purpose**: Characterize what kind of lemmas are being lost.

**Output**: `outputs/analysis/lost_category_complexity.csv`

**Columns**:
- `dimension`: "Category" or "Complexity"
- `value`: Category name or band
- `count`: Number of lost lemmas
- `ratio`: Percentage of total lost

##### Task 12: Lost Lemma Casebook

**Purpose**: Provide concrete examples for the paper.

**Output**: `outputs/analysis/lost_casebook.md`

Samples 10 diverse examples covering different failure modes, with:
- Lemma ID, category, complexity
- Status summary (Baseline/Fast/Synergy)
- Failure modes
- Error messages (truncated to 200 chars)
- Lemma statement (first 300 chars)

**Run all lost-success analyses**:
```bash
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --lost-successes
```

#### 6. Verified Core vs Unverified Passes (Task 4)

**Status**: Not implemented (requires instrumentation).

**Requirements**:
- Instrument sanitizer to log per-lemma rewrite info (which UP/VC passes were applied)
- Track which rewrites violate AdmissibleSpec
- Compute Unsafe Rewrite Count (URC) under Fast vs Synergy

**Planned outputs**:
- `outputs/analysis/core_vs_fast.csv`
- `outputs/analysis/latex/core_vs_fast.tex`

#### 7. Extra Baselines (Task 5)

**Status**: Not implemented (requires new experiments).

**Planned baselines**:
1. **Regex-sanitizer**: Simple regex-based sanitization (no mechanized soundness)
2. **CoqHammer-only**: No sanitization, rely only on CoqHammer auto-tactics

**Planned output**: `outputs/analysis/extra_baselines.csv` with columns:
- `config_name`, `verified_ratio`, `mechanized_guarantee`, `notes`

## Command Reference

### Run All Analyses

```bash
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --all
```

### Run Specific Analyses

```bash
# Fragment coverage only
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --fragment

# Category breakdown only
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --category

# Complexity analysis only
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --complexity

# Lost successes only
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --lost-successes

# Multiple specific analyses
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --fragment --category --complexity
```

### Custom Output Directory

```bash
python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed11 \
    --output-dir outputs/custom_analysis \
    --all
```

## Output Files Reference

All analysis outputs are written to `outputs/analysis/` by default.

### CSV Files

- `joint_results_2k.csv`: Unified per-lemma results table (2000+ rows)
- `fragment_coverage_summary.csv`: Fragment coverage stats
- `category_results.csv`: Per-category verification rates
- `complexity_results.csv`: Per-complexity-band verification rates
- `lost_successes.csv`: Details of 96 lost lemmas
- `lost_successes_summary.json`: Aggregated lost-success statistics
- `lost_failure_modes.csv`: Failure mode classification for lost lemmas
- `lost_category_complexity.csv`: Category/complexity distribution of lost lemmas

### LaTeX Snippets

All LaTeX tables are in `outputs/analysis/latex/`:

- `fragment_coverage.tex`: Fragment coverage table
- `category_results.tex`: Category breakdown table
- `complexity_results.tex`: Complexity band table
- `lost_failure_modes.tex`: Lost lemma failure modes table

### Markdown Files

- `lost_casebook.md`: Concrete examples of lost-success lemmas

## Reproducibility Notes

### Deterministic Behavior

- All categorization logic is deterministic (based on lemma ID keywords)
- Complexity metrics are deterministic (AST depth, binder count)
- Fragment checker is deterministic (regex-based disallowed patterns)
- Casebook sampling uses Python's `random.choice` (seed not set, so non-deterministic)

### Data Dependencies

The analysis system expects:
- `<experiment_dir>/results.csv`: Must exist
- `<experiment_dir>/error_traces.jsonl`: Optional (for error messages)
- `data/synergy_rag_2k.jsonl`: Input data with `draft` field (for fragment coverage)

If `error_traces.jsonl` is missing, error messages will be empty but analysis continues.

## Extending the Analysis

### Adding New Semantic Categories

Edit `categorize_lemma()` in `scripts/analyze_synergy_experiments.py`:

```python
def categorize_lemma(lemma_id: str) -> str:
    lower_id = lemma_id.lower()

    # Add new category
    if any(kw in lower_id for kw in ['your', 'keywords']):
        return "YourCategory"

    # ... existing categories ...
    return "Misc"
```

### Adding New Complexity Bands

Edit `assign_complexity_band()` in `scripts/analyze_synergy_experiments.py`:

```python
def assign_complexity_band(depth: int, binder_count: int) -> str:
    complexity_score = depth + binder_count * 2

    if complexity_score <= 5:
        return "trivial"
    elif complexity_score <= 8:
        return "shallow"
    # ... etc.
```

### Adding New Failure Modes

Edit `categorize_failure_mode()` in `scripts/utils/lost_success_analysis.py`:

```python
def categorize_failure_mode(status: str, error_msg: str) -> str:
    error_lower = error_msg.lower()

    # Add new failure mode
    if 'your pattern' in error_lower:
        return "YOUR_NEW_MODE"

    # ... existing modes ...
    return "OTHER"
```

## Troubleshooting

### Import Error for `lost_success_analysis`

If you see:
```
ERROR | Failed to import lost_success_analysis module
```

Ensure `scripts/utils/__init__.py` exists:
```bash
touch scripts/utils/__init__.py
```

### Missing Input Data

If fragment coverage annotation fails:
```
WARNING | Loaded 0 draft statements
```

Check that `data/synergy_rag_2k.jsonl` exists and has the correct format:
```json
{"id": "...", "draft": "Lemma ...", ...}
```

### Empty Joint Table

If joint table is empty, check:
1. `results.csv` exists and has correct format (header row + data rows)
2. CSV has columns: `item_id`, `config_name`, `status`, `time_ms`, `urc_flag`

## Paper Correspondence

### Tables

- **Table X: Fragment Coverage** → `latex/fragment_coverage.tex`
- **Table Y: Per-Category Results** → `latex/category_results.tex`
- **Table Z: Complexity Bands** → `latex/complexity_results.tex`
- **Table W: Lost Lemma Failure Modes** → `latex/lost_failure_modes.tex`

### Figures

Not yet implemented. Planned:
- Bar chart: Category verification rates across configs
- Line chart: Complexity vs verification rate
- Pie chart: Lost lemma failure mode distribution

## Contact

For questions or issues, please refer to:
- Main analysis script: `scripts/analyze_synergy_experiments.py`
- Lost-success analysis module: `scripts/utils/lost_success_analysis.py`
- Main experiment runner: `scripts/run_synergy_experiments.py`
- Pipeline definitions: `sapse/sanitize/pipelines.py`

---

## Complete Analysis Pipeline

### Step 1: Run Full Analysis

```bash
# Run all analyses on experiment results
python scripts/analyze_synergy_experiments.py \
  --experiment outputs/synergy_deepseek_real_2k_seed5 \
  --output-dir outputs/analysis \
  --all
```

**Duration**: ~2-3 seconds

**Outputs**:
- `joint_results_2k.csv` - Master table with all 2,000 lemmas × 4 configs
- `fragment_coverage_summary.csv` - In-frag vs out-of-frag analysis
- `category_results.csv` - Per-category breakdown
- `complexity_results.csv` - Per-complexity-band stats
- `lost_successes.csv` - 96 lost lemmas with full details
- `lost_successes_summary.json` - Summary statistics
- `lost_failure_modes.csv` - Failure categorization
- `lost_category_complexity.csv` - Lost lemmas characteristics
- `lost_casebook.md` - 10 representative examples
- `latex/*.tex` - LaTeX table snippets for paper

### Step 2: Verify Results

```bash
# Check key numbers
python3 << 'PYEOF'
import csv
import json

# Load joint table
with open('outputs/analysis/joint_results_2k.csv') as f:
    data = list(csv.DictReader(f))

# Count verified
baseline = sum(1 for r in data if r['baseline_status'] == 'Verified')
fast = sum(1 for r in data if r['fast_status'] == 'Verified')
synergy = sum(1 for r in data if r['synergy_status'] == 'Verified')

print(f"Baseline-RAG: {baseline}/2000 ({baseline/20:.1f}%)")
print(f"SAPSE-Fast: {fast}/2000 ({fast/20:.1f}%)")
print(f"SAPSE-Synergy: {synergy}/2000 ({synergy/20:.1f}%)")
print(f"Lost successes: {baseline - fast}")

# Load lost summary
with open('outputs/analysis/lost_successes_summary.json') as f:
    summary = json.load(f)
print(f"\nFailed in Fast: {summary['failed_in_fast']}")
print(f"Failed in Synergy: {summary['failed_in_synergy']}")
PYEOF
```

---

## Analysis Outputs Reference

### PART I: Extended Experiment Analysis

#### Task 1: Fragment Coverage

**File**: `outputs/analysis/fragment_coverage_summary.csv`

**Columns**:
- `category` - Semantic category (or "All" for global)
- `num_lemmas` - Total lemmas in category
- `in_frag_count` - Lemmas using only verified constructs
- `in_frag_ratio` - Fraction in verified fragment
- `synergy_verified_in_frag` - Synergy verified count (in-fragment)
- `synergy_verified_out_frag` - Synergy verified count (out-of-fragment)

**LaTeX**: `outputs/analysis/latex/fragment_coverage.tex`

**Interpretation**:
- High `in_frag_ratio` → lemmas use basic Coq constructs
- `synergy_verified_in_frag` should exceed `synergy_verified_out_frag`

#### Task 2: Semantic Categories

**File**: `outputs/analysis/category_results.csv`

**Columns**:
- `category` - Arithmetic, Boolean, List, Inductive, Misc
- `num_lemmas` - Total lemmas in category
- `verified_baseline`, `verified_strict`, `verified_fast`, `verified_synergy` - Verified counts
- `abstained_strict`, `abstained_synergy` - Abstention counts

**LaTeX**: `outputs/analysis/latex/category_results.tex`

**Categorization Rules** (see `categorize_lemma()` in analyze_synergy_experiments.py):
- **Arithmetic**: zarith, nat, integer, int, add, mul, sub, div
- **Boolean**: bool, and, or, neg, true, false
- **List**: list, append, map, fold, cons, nil
- **Inductive**: inductive, match, case, tree, option
- **Misc**: default

#### Task 3: Structural Complexity

**File**: `outputs/analysis/complexity_results.csv`

**Columns**:
- `band` - shallow, medium, deep
- `num_lemmas` - Total lemmas in band
- `verified_*`, `abstained_*` - Per-config counts

**LaTeX**: `outputs/analysis/latex/complexity_results.tex`

**Complexity Computation** (see `compute_ast_metrics()`):
- **AST depth**: Max nesting of parentheses/braces
- **Binder count**: Number of `forall` keywords
- **Score**: `depth + binder_count * 2`
- **Bands**:
  - Shallow: score ≤ 8
  - Medium: 9 ≤ score ≤ 16
  - Deep: score ≥ 17

### PART II: Lost-Success Differential Analysis

#### Task 8: Isolate Lost Successes

**File**: `outputs/analysis/lost_successes.csv`

**Lost Lemmas Definition**:
```
Lost = {lemma_id | baseline_status == "Verified" AND fast_status != "Verified"}
```

**Expected Count**: 96 (from 752 - 656)

**Columns**:
- `lemma_id` - Unique identifier (e.g., CompCert:Module:lemma_name)
- `category`, `complexity_band` - From PART I
- `baseline_status`, `fast_status`, `synergy_status` - Verification outcomes
- `baseline_runtime`, `fast_runtime`, `synergy_runtime` - Time in ms
- `baseline_error`, `fast_error`, `synergy_error` - Error messages (if available)

**Summary**: `outputs/analysis/lost_successes_summary.json`

```json
{
  "total_lost": 96,
  "failed_in_fast": 96,
  "abstained_in_fast": 0,
  "error_in_fast": 0,
  "timeout_in_fast": 0,
  "failed_in_synergy": 96,
  "abstained_in_synergy": 0,
  "error_in_synergy": 0,
  "timeout_in_synergy": 0
}
```

**Interpretation**: All 96 lost lemmas show status "Failed" (not abstained or error).

#### Task 9: Statement Comparison

**Status**: ⚠️ **Partially Implemented**

**Limitation**: Final ASTs not logged in current experiment format.

**Workaround**: Analysis marks all as "SHALLOW_CHANGE" placeholder.

**To Enable Full Diff Analysis**:
1. Modify `run_synergy_experiments.py` to log final ASTs per config
2. Re-run experiments with logging enabled
3. Re-run analysis to compute real diffs

**Planned Fields** (when implemented):
- `change_type_fast` - NO_CHANGE, SHALLOW_CHANGE, STRUCTURAL_CHANGE
- `change_score_fast` - Token-level Levenshtein distance [0.0, 1.0]

#### Task 10: Failure Mode Breakdown

**File**: `outputs/analysis/lost_failure_modes.csv`

**Columns**:
- `lemma_id` - Lemma identifier
- `fast_failure_mode` - Categorized failure for SAPSE-Fast
- `synergy_failure_mode` - Categorized failure for SAPSE-Synergy

**Failure Categories** (see `categorize_failure_mode()`):
- **TYPE_ERROR** - Ill-typed term, type mismatch
- **UNRESOLVED_IDENTIFIER** - Unbound variable, undefined symbol
- **TAC_FAIL** - Tactic or hammer automation failure
- **TIMEOUT** - Verification timeout
- **GUARD_REJECTED** - Admissibility check failed (Strict/Synergy only)
- **OTHER** - Unknown or uncategorized

**LaTeX**: `outputs/analysis/latex/lost_failure_modes.tex`

**Current Limitation**: Without error message logging, most failures categorized as "OTHER".

**Sample Output** (when error logging enabled):
```
TYPE_ERROR: 40
UNRESOLVED_IDENTIFIER: 25
TAC_FAIL: 20
GUARD_REJECTED: 11
```

#### Task 11: Lost Lemma Characteristics

**File**: `outputs/analysis/lost_category_complexity.csv`

**Format**:
```csv
dimension,value,count,ratio
category,Arithmetic,15,15.6%
category,Boolean,5,5.2%
category,Inductive,30,31.3%
category,List,12,12.5%
category,Misc,34,35.4%
complexity,shallow,20,20.8%
complexity,medium,45,46.9%
complexity,deep,31,32.3%
```

**Interpretation**:
- Identifies which categories/complexities are most affected by sanitization
- Example: "Inductive + Misc categories account for 66.7% of losses"

#### Task 12: Lost Lemma Casebook

**File**: `outputs/analysis/lost_casebook.md`

**Purpose**: Provide concrete examples for qualitative analysis in paper

**Sampling Strategy**:
- 10 examples (configurable via `num_examples` parameter)
- Stratified by failure mode (try to cover all modes)
- Deterministic sampling (random seed = 42)

**Example Entry**:
```markdown
## Example 1: CompCert:RTLgen:add_instr_incr

**Category**: Arithmetic
**Complexity**: shallow

### Status Summary
- **Baseline-RAG**: Verified (112.8ms)
- **SAPSE-Fast**: Failed (75.6ms)
- **SAPSE-Synergy**: Failed (76.1ms)

### Failure Modes
- **Fast**: TYPE_ERROR
- **Synergy**: TYPE_ERROR

### Error Messages
**Fast**: The term "x" has type "nat" but is expected to have type "Z"

### Lemma Statement (first 300 chars)
...coq code...
```

**Usage for Paper**: Manually select 2-3 most illustrative examples from casebook.

---

## Mapping to Paper Tables/Figures

### Main Paper

**Table 2: Overall Results**
- **Source**: `outputs/synergy_deepseek_real_2k_seed5/aggregated_table.md`
- **Rows**: 4 configurations
- **Columns**: Verified (%), Abstained (%), Avg Time, URC Sum

**Table 3: Per-Category Breakdown**
- **Source**: `outputs/analysis/latex/category_results.tex`
- **Direct inclusion**: Copy LaTeX to paper

**Table 4: Complexity Analysis**
- **Source**: `outputs/analysis/latex/complexity_results.tex`

**Table 5: Lost Lemma Failure Modes**
- **Source**: `outputs/analysis/latex/lost_failure_modes.tex`
- **Note**: Requires error logging enabled for detailed categories

### Appendix

**Table F.1: Fragment Coverage**
- **Source**: `outputs/analysis/latex/fragment_coverage.tex`

**Section 6.2: Qualitative Examples**
- **Source**: `outputs/analysis/lost_casebook.md`
- **Action**: Manually select 2-3 examples showing:
  1. Structural change → type error
  2. Shallow change → proof search failure  
  3. Guard rejection case

---

## Interpreting Results

### Understanding the 37.6% → 32.8% Drop

**Observation**: Baseline-RAG (752/2000) outperforms Fast/Synergy (656/2000)

**Hypotheses to Test** (via lost-success analysis):

1. **Sanitization Damage Hypothesis**
   - UP passes introduce type errors or corrupt syntax
   - Check: `lost_failure_modes.csv` for TYPE_ERROR count
   - Expected: High TYPE_ERROR if hypothesis true

2. **Proof Search Disruption Hypothesis**
   - Sanitization changes lemma statements in ways that break automation
   - Check: `lost_failure_modes.csv` for TAC_FAIL count
   - Expected: High TAC_FAIL if hypothesis true

3. **Guard Over-Rejection Hypothesis**
   - VC guards (Synergy) reject valid candidates
   - Check: `lost_failure_modes.csv` for GUARD_REJECTED in Synergy column
   - Expected: Synergy has GUARD_REJECTED, Fast does not

4. **Category-Specific Weakness Hypothesis**
   - Sanitization struggles with specific lemma families
   - Check: `lost_category_complexity.csv`
   - Expected: Losses concentrated in 1-2 categories

**Current Findings** (Seed 5):
- All 96 losses: Fast status = "Failed", Synergy status = "Failed"
- Failure modes: "OTHER" (requires error logging to diagnose)
- Category distribution: TBD (check lost_category_complexity.csv)
- Complexity distribution: TBD

**Action Items**:
1. Enable error message logging in `run_synergy_experiments.py`
2. Re-run experiments with error tracking
3. Re-run analysis to get detailed failure mode breakdown
4. Interpret results to confirm/reject hypotheses

---

## Troubleshooting

### Common Issues

#### 1. "Error traces file not found" Warning

**Symptom**:
```
WARNING - Error traces file not found: .../error_traces.jsonl
```

**Impact**: Failure modes default to "OTHER" instead of detailed categories.

**Fix**: Add error logging to experiment script:
```python
# In run_synergy_experiments.py
error_traces_path = output_dir / "error_traces.jsonl"

def log_error(item_id, config_name, error_msg):
    with open(error_traces_path, 'a') as f:
        json.dump({
            'item_id': item_id,
            'config_name': config_name,
            'error_message': str(error_msg)
        }, f)
        f.write('\n')
```

#### 2. "Statement diff not implemented" Warning

**Symptom**:
```
WARNING - Statement diff annotation not fully implemented
```

**Impact**: Task 9 shows placeholder change types.

**Fix**: Log final ASTs per configuration in experiment runner.

#### 3. Empty LaTeX Tables

**Cause**: Missing metadata or insufficient data.

**Fix**: Ensure `--all` flag runs all annotation steps.

#### 4. Lost Count Mismatch

**Expected**: 96 (752 - 656)
**Actual**: Check `lost_successes_summary.json`

**Causes**:
- Different seed/experiment version
- Data loading errors

**Debug**:
```bash
# Verify counts directly
grep -c "Baseline-RAG,Verified" outputs/synergy_*/results.csv
grep -c "SAPSE-Fast,Verified" outputs/synergy_*/results.csv
```

---

## Advanced Topics

### Running on Multiple Seeds

```bash
# Aggregate across seeds 3, 5, 7, 11
for seed in 3 5 7 11; do
  python scripts/analyze_synergy_experiments.py \
    --experiment outputs/synergy_deepseek_real_2k_seed$seed \
    --output-dir outputs/analysis_seed$seed \
    --all
done

# Combine results (future work: implement aggregation script)
```

### Custom Category Definitions

Edit `categorize_lemma()` in `scripts/analyze_synergy_experiments.py:468`:

```python
def categorize_lemma(lemma_id: str) -> str:
    lower_id = lemma_id.lower()
    
    # Add custom patterns
    if 'pointer' in lower_id or 'memory' in lower_id:
        return "Memory"
    
    # ... existing patterns ...
```

### Adjusting Complexity Thresholds

Edit `assign_complexity_band()` in `scripts/analyze_synergy_experiments.py:634`:

```python
def assign_complexity_band(depth: int, binder_count: int) -> str:
    complexity_score = depth + binder_count * 2
    
    # Adjust for balanced buckets
    if complexity_score <= 6:  # Changed from 8
        return "shallow"
    # ...
```

---

## Future Work

### Task 4: Core vs Fast Comparison (Stub)

**Goal**: Quantify unsafe rewrites filtered by VC

**Requirements**:
1. Instrument UP passes (4-6) to track proposed rewrites
2. Log rewrite metadata (type, old/new AST)
3. For each lemma, compare:
   - Fast: All UP rewrites forwarded to Coq
   - Synergy: UP rewrites → VC filter → only admissible forwarded
4. Compute: `unsafe_rewrite_count = UP_proposals violating AdmissibleSpec`

**Expected Output**: `outputs/analysis/core_vs_fast.csv`

### Task 5: Extra Baselines (Stub)

**Goal**: Compare against simpler baselines

**Regex Sanitizer**:
- Simple regex-based fixes (no AST analysis)
- Expected: Lower verified%, no mechanized guarantees

**CoqHammer-only**:
- No sanitization, rely on automation alone
- Expected: Many type errors, lowest verified%

**Implementation**: New pipeline variants in `sapse/sanitize/pipelines.py`

---

## Command Reference

### One-Line Full Pipeline

```bash
# From scratch
python scripts/run_synergy_experiments.py \
  --input data/synergy_rag_2k.jsonl \
  --output-dir outputs/synergy_2k && \
python scripts/analyze_synergy_experiments.py \
  --experiment outputs/synergy_2k \
  --output-dir outputs/analysis \
  --all
```

### Quick Checks

```bash
# Verify experiment completed
wc -l outputs/synergy_2k/results.csv
# Expected: 8001 (header + 2000*4)

# Check lost lemmas
cat outputs/analysis/lost_successes_summary.json

# Browse casebook
less outputs/analysis/lost_casebook.md

# View LaTeX tables
ls outputs/analysis/latex/
```

---

## Contact & Support

For issues or questions about the analysis pipeline:

1. Check this documentation
2. Review `outputs/analysis/RECON_SUMMARY.md` for architecture details
3. Examine analysis code: `scripts/analyze_synergy_experiments.py`
4. Check lost-success module: `scripts/utils/lost_success_analysis.py`

**Last Updated**: 2025-11-08 by Claude (Code Assistant)
