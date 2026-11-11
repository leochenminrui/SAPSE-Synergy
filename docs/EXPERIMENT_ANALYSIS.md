# Benchmark analysis

Use the supplied reference tables in `outputs/analysis/` to inspect category,
complexity, fragment-coverage, and lost-success summaries. The associated numeric
LaTeX tables are display generators' outputs, not manuscript source projects.

To analyze a newly completed evaluation, run from the repository root:

```bash
PYTHONPATH=python python python/scripts/analyze_synergy_experiments.py \
  --experiment outputs/reproduction_run \
  --input data/input/synergy_rag_2k.jsonl \
  --output-dir outputs/analysis_reproduction \
  --fragment --category --complexity --lost-successes
```

The experiment directory must contain `results.csv`, with columns `item_id`,
`config_name`, `status`, `time_ms`, and `urc_flag`. Optional
`error_traces.jsonl` supplies per-mode errors and available AST details. The input
JSONL supplies draft statements for fragment annotation. Use an explicit
`--input` when analyzing a different dataset. All four modes must use matching
lemma IDs for a meaningful differential comparison.

The analysis writes an aligned `joint_results_2k.csv`, category and complexity
summaries, fragment summaries, a lost-success table/casebook, and LaTeX summary
tables. Category labels follow name-based rules; structural bands follow the
implemented checker. All supplied 2,000 records are in its shallow band, so these
records do not establish a complexity trend across multiple bands.

The saved results contain 96 Baseline-RAG successes that fail in both Fast and
Synergy. The archived casebook has no detailed error messages and labels failure
modes `OTHER`; it should be used to locate examples, not to infer percentages of
type errors, timeouts, or guard rejections. Newly generated error traces can
support a more specific analysis when the underlying errors are available.

`--core-vs-fast` and `--baselines` are retained CLI placeholders and do not run
additional experiments. The documented command selects implemented analyses
explicitly. See the [reproduction guide](ARTIFACT.md) for reference identities,
formal scope, and comparisons with the paper.
