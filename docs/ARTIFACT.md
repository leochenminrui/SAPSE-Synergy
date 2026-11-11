# Reproduction guide

This repository accompanies the [published FM 2026 paper](https://doi.org/10.1007/978-3-032-26204-2_8).
The supported entry points are a build of the five mechanized theories,
evaluation of four sanitizer modes on the fixed 2,000-draft input, and analysis of
saved benchmark records. The benchmark starts after retrieval and generation;
recreating the original corpus extraction, embeddings, or LLM generation requires
additional inputs and is not part of this fixed-draft evaluation.

## Environment

Run the commands below from the repository root. Use Python 3.10 or later and an
isolated environment:

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r python/requirements-evaluation.txt
```

The evaluation requirements are pinned and were tested with Python 3.12. The
paper used Rocq 9.1.0. The source build and 10-draft smoke run were also checked
with Rocq 9.1.1; different prover versions can change verification outcomes. Put
`coqc` and `coq_makefile` from the selected Rocq installation on `PATH` and check:

```bash
coqc --version
coq_makefile --help
```

A CPU is sufficient for the fixed-draft experiment; no GPU, embedding-model
download, API key, or billed generation call is needed. The original guide
allocated 3–6 hours for a full run with a 30-second per-goal timeout. Actual
runtime depends on failures, prover version, and hardware; a 10-draft run checks
functionality only. The optional retrieval/generation modules have additional
requirements in `python/requirements.txt` and may download models or call APIs
when explicitly configured.

## 1. Check the supplied evidence

```bash
python python/scripts/verify_reference_results.py
```

This standard-library command verifies the SHA-256 manifests, 2,000 distinct
input IDs, 8,000 saved outcome rows, per-mode status counts, 96 lost successes,
and the saved fragment-coverage summary. It checks archived evidence; it does
not rerun proof checking or infer the semantic adequacy of generated statements.

| Record | Role |
| --- | --- |
| `data/input/synergy_rag_2k.jsonl` | Fixed generated Coq drafts; each record has `id` and `draft` |
| `outputs/full_results_seed5.csv` | Authoritative combined single-seed outcomes, 8,000 rows |
| `outputs/aggregated_results.md` | Human-readable aggregate of those outcomes |
| `outputs/analysis/joint_results_2k.csv` | Saved aligned per-lemma analysis |
| `outputs/analysis/fragment_coverage_summary.csv` | Saved 1,962/2,000 fragment summary |
| `outputs/analysis/lost_successes.csv` | Saved 96-item differential subset |
| `data/SHA256SUMS`, `outputs/SHA256SUMS` | Exact input and reference-file identities |

The saved outcomes and input were retained from source commit
`770c8a397ed78190efc95f19b7b1b6de5c46c328`. That commit identifies the original
public tree, not a separate software release DOI. Record the current commit when
reporting a new run.

## 2. Build the mechanized core

```bash
make -C coq
```

The build regenerates a local toolchain-specific Makefile and compiles `Syntax`,
`Typing`, `Semantics`, `Sanitizer`, and `Soundness`. See the
[formalization guide](../coq/README.md) for the actual theorem and assumptions.
Compiler output is generated locally, rather than supplied as evidence of a
successful build. Rebuild from scratch with `make -C coq clean` followed by
`make -C coq`.

## 3. Evaluate supplied drafts

```bash
# Real Coq smoke evaluation: 10 drafts, 4 modes, 40 outcome rows
bash python/run_full_experiment.sh --limit 10

# Full fixed-draft evaluation: 2,000 drafts, 4 modes, 8,000 outcome rows
bash python/run_full_experiment.sh
```

The wrapper accepts only an optional positive `--limit N`. It resolves its paths
relative to the repository, sets the Python import path, requires a real `coqc`,
and passes the saved run's seed 5 and 30-second timeout. It refuses to report a
mock-verifier fallback as a real evaluation. The outputs are:

- `outputs/reproduction_run/results.csv`
- `outputs/reproduction_run/error_traces.jsonl`
- `outputs/reproduction_run/aggregated_table.md`
- `outputs/analysis_reproduction/` (CSV/LaTeX summaries and lost-success casebook)

These generated directories are ignored by Git so the supplied reference records
remain intact. For a custom input or output directory, use the underlying CLI:

```bash
PYTHONPATH=python python python/scripts/run_synergy_experiments.py \
  --input data/input/synergy_rag_2k.jsonl \
  --output-dir outputs/reproduction_run \
  --coq-random-seed 5 --coq-timeout 30
```

The CLI also provides `--use-mock-verifier` for a labeled software demonstration.
Mock results are synthetic and cannot verify the paper's findings.

## 4. Compare a full run

Read the new aggregate and the reference:

```bash
cat outputs/reproduction_run/aggregated_table.md
cat outputs/aggregated_results.md
```

The single-seed reference has 752, 746, 656, and 656 verified drafts in
Baseline-RAG, Strict, Fast, and Synergy, respectively. The corresponding abstention
counts are 0, 106, 0, and 1. Compare per-item outcomes and denominators as well as
aggregate percentages. Runtime values depend on the environment and should not
be expected to match byte for byte. Investigate outcome differences rather than
changing the reference counts or selecting a new population.

The analysis entry point is documented in the [analysis guide](EXPERIMENT_ANALYSIS.md).
Its fragment checker operates on draft text and optional final-AST traces. The
supplied historical fragment summary is a separate reference: a fresh run without
identical final-AST instrumentation must not be represented as reconstructing that
summary exactly. The saved casebook lacks detailed error traces, so its `OTHER`
failure labels do not establish a causal breakdown of the 96 losses.

## Interpretation

The Rocq theorem proves preservation under explicit typing and well-formedness
assumptions in a minimal calculus with right-appended context extensions. It does not prove
that natural-language intent survived generation or heuristic repairs, or that
the Python regex implementation is extracted from the mechanized definitions.
The recorded `urc_flag` is an implementation diagnostic; zero flags alone are
not a formal proof of the entire pipeline.

## Verification record

The repository cleanup checks are recorded in [VERIFICATION.md](VERIFICATION.md).
They distinguish saved-record checks, compilation, and a small real-prover run
from a new complete experiment. The paper describes multiple seeds; this release
contains the single saved seed-5 outcome set and does not reconstruct the
cross-seed study from those records alone.
