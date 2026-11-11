# SAPSE-Synergy

**A retrieval and verification pipeline connecting neural theorem proving with formal proof checking.**

SAPSE-Synergy studies how generated Coq lemmas can be repaired while keeping the
scope of formal guarantees explicit. Its Rocq development proves typing and
logical-equivalence preservation for an AST sanitizer in a minimal calculus. The
Python implementation compares direct verification, guarded core transformations,
heuristic repairs, and their composition on the same lemma drafts.

Use this repository to inspect and build the mechanized core, evaluate sanitizer
modes on supplied Coq drafts, and analyze the accompanying 2,000-lemma benchmark.
Retrieval and embedding modules are also provided for experiments with your own
licensed corpus.

**Paper:** Minrui Chen, Huidong Jiang, and Hiroto Saigo.
*SAPSE-Synergy: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving.*
FM 2026, LNCS 16556, pp. 151–169.
[Read the published paper](https://doi.org/10.1007/978-3-032-26204-2_8).

[Quick start](#quick-start) · [Results](#benchmark-results) ·
[Reproduction guide](docs/ARTIFACT.md) · [Citation](#citation) · [License](#license)

## Method

The sanitizer separates require injection, equality canonicalization, and a
binder-normalization schema from heuristic scope, list, and formatting repairs.
The current mechanized binder pass is the identity. The Synergy mode runs the
heuristic utilities before the guarded core and then submits the candidate to
Coq. The soundness theorem concerns admissible transformations in the modeled
calculus; retrieval, generation, and the preceding heuristic repairs remain
empirical components.

## Quick start

Clone the repository and use Python 3.10 or later. The evaluation requirements
below are tested with Python 3.12. They do not download embedding models or call
an LLM API.

```bash
git clone https://github.com/leochenminrui/SAPSE-Synergy.git
cd SAPSE-Synergy
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r python/requirements-evaluation.txt
```

First, check the supplied benchmark records using only the Python standard library:

```bash
python python/scripts/verify_reference_results.py
```

This checks all 8,000 saved outcomes, the 2,000 unique lemma IDs, the 96 lost
successes, and the saved fragment-coverage summary.

To build the five mechanized theories, install Rocq 9.1.x with the `coqc` and
`coq_makefile` compatibility commands on `PATH`:

```bash
make -C coq
```

To run a small **real Coq** evaluation on the first 10 supplied drafts:

```bash
bash python/run_full_experiment.sh --limit 10
```

The input is `data/input/synergy_rag_2k.jsonl`. Each item supplies an `id` and a
`draft` containing Coq source, for example:

```json
{"id": "example", "draft": "Lemma example : True. Proof. exact I. Qed."}
```

The runner writes one outcome per item and mode to
`outputs/reproduction_run/results.csv`, with columns
`item_id,config_name,status,time_ms,urc_flag`, plus an aggregate Markdown table and
analysis files. Ten drafts produce 40 outcome rows; this is a functionality check,
not an estimate of the full benchmark's verification rates. See the
[reproduction guide](docs/ARTIFACT.md) for full evaluation, dependencies, and
reference comparisons.

## Benchmark results

The supplied single-seed records contain 2,000 drafts evaluated in four modes:

| Mode | Transformation path | Verified | Abstained |
| --- | --- | ---: | ---: |
| Baseline-RAG | Direct Coq checking | 752 / 2,000 (37.6%) | 0 (0.0%) |
| SAPSE-Strict | Guarded core | 746 / 2,000 (37.3%) | 106 (5.3%) |
| SAPSE-Fast | Heuristic utilities | 656 / 2,000 (32.8%) | 0 (0.0%) |
| SAPSE-Synergy | Utilities followed by guarded core | 656 / 2,000 (32.8%) | 1 (0.1%) |

Synergy exposes a 4.8 percentage-point coverage gap from Baseline-RAG, comprising
96 baseline successes that fail in both Fast and Synergy. The saved fragment
analysis places 1,962 / 2,000 lemmas (98.1%) inside the mechanized fragment,
including all 656 Synergy successes. The benchmark reports zero unsafe rewrites
among guarded repairs. This result identifies a safety–coverage trade-off rather
than an improvement in raw verification rate.

See [saved aggregate results](outputs/aggregated_results.md), the
[lost-success casebook](outputs/analysis/lost_casebook.md), and the
[analysis guide](docs/EXPERIMENT_ANALYSIS.md).

## Code and reproducibility artifact

- [`coq/theories/`](coq/theories/): calculus, sanitizer, and composite soundness theorem.
- [`python/sapse/`](python/sapse/): retrieval, embeddings, sanitization, and verification.
- [`python/scripts/`](python/scripts/): benchmark runner, analysis, and reference checks.
- [`data/input/`](data/input/): fixed, pre-generated benchmark drafts.
- [`outputs/`](outputs/): saved outcomes and compact analysis references.
- [Reproduction guide](docs/ARTIFACT.md): exact commands, environment, provenance,
  expected outputs, and verification scope.

The benchmark starts from supplied drafts and needs neither generation API keys
nor a retrieval index. To use the broader retrieval modules, install
`python/requirements.txt` and supply your own corpus or index as described in the
[data guide](data/README.md).

## Citation

If you use SAPSE-Synergy, its sanitizer, or the benchmark in research, cite the
**published FM 2026 paper**:

> Chen, M., Jiang, H., and Saigo, H. (2026). SAPSE-Synergy: Balancing Formal
> Soundness and Empirical Coverage in Neural Theorem Proving. In *Formal Methods*,
> LNCS 16556, pp. 151–169. https://doi.org/10.1007/978-3-032-26204-2_8

```bibtex
@inproceedings{chen2026sapse,
  author    = {Chen, Minrui and Jiang, Huidong and Saigo, Hiroto},
  title     = {{SAPSE-Synergy}: Balancing Formal Soundness and Empirical Coverage in Neural Theorem Proving},
  booktitle = {Formal Methods},
  editor    = {Sampaio, Augusto and Stoelinga, Mariëlle},
  series    = {Lecture Notes in Computer Science},
  volume    = {16556},
  pages     = {151--169},
  year      = {2026},
  publisher = {Springer Nature Switzerland},
  doi       = {10.1007/978-3-032-26204-2_8},
  url       = {https://doi.org/10.1007/978-3-032-26204-2_8}
}
```

[`CITATION.cff`](CITATION.cff) supplies the same paper as the preferred citation
for GitHub's **Cite this repository** feature. For a computational study, also
record the commit used; the paper DOI identifies the publication, not a software
version.

## License

Project code is distributed under the [MIT License](LICENSE). Source-derived
benchmark text and upstream dependencies retain their respective terms; the code
license does not relicense third-party material. See the [data guide](data/README.md)
and [third-party notices](THIRD_PARTY_NOTICES.md).
