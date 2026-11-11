# Verification record

Checked on 2026-11-11 with Python 3.12.14 and Rocq 9.1.1 on macOS arm64.
The evaluation environment is declared in `python/requirements-evaluation.txt`.
The paper's prover version is Rocq 9.1.0.

| Check | Outcome |
| --- | --- |
| Standard-library reference check | Passed: 2,000 distinct input IDs, 8,000 outcomes, per-mode counts, 96 lost successes, saved 98.1% fragment summary, and input/output SHA-256 manifests |
| Clean source build | Passed: all five Rocq theories compiled from `.v` source |
| Real-prover smoke run | Passed: first 10 drafts × 4 modes = 40 outcomes, aggregate table, error traces, and implemented analyses |
| Missing-prover check | Passed: a nonexistent `--coqc-path` fails explicitly; it cannot silently produce mock benchmark results |
| Citation metadata | Passed against the official Citation File Format 1.2.0 JSON schema; publication metadata checked against Springer and Crossref |
| Shell syntax and whitespace | Passed: `bash -n python/run_full_experiment.sh` and `git diff --check` |
| Existing focused Python tests | 31 passed, 1 failed; see below |

The source archive was exported from the staged release tree and checked after
extraction into a separate directory, with a fresh environment installed from
the declared evaluation requirements. Generated compiler files, Python caches,
local machine configuration, and fresh smoke-run outputs are excluded from the
release tree. The supplied scientific inputs and reference outcomes retain their
original bytes.

## Existing test failure

```bash
PYTHONPATH=python python -m pytest \
  python/tests/test_synergy_pipelines.py \
  python/tests/test_ast_sanitizer.py \
  python/tests/test_verify_mock.py -q
```

`TestASTSanitizer.test_fill_missing_types_nat` fails because the auxiliary
`ASTSanitizer` does not infer types for `forall n m` in that test. The same test
fails against the unchanged original source commit
`770c8a397ed78190efc95f19b7b1b6de5c46c328`. The four-mode experiment uses
`sapse.sanitize.pipelines` and its passes, rather than this auxiliary sanitizer.
The failure is retained; no test is skipped or marked as an expected failure,
and the scientific transformation code is unchanged by repository packaging.

The removed `test_cli_flags_exist.py` referenced `scripts/evaluate.py` and
`scripts/plot_comparison.py`, neither of which exists in this repository. Tests
for the actual sanitizer and verifier remain available.

## Scope

The 10-draft smoke run verified 2 drafts in Baseline-RAG and 2 in Strict; Strict
abstained on 3, and Fast and Synergy verified 0. These are subset functionality
results and are not estimates of the paper's full benchmark rates. The full
2,000-draft experiment, all paper seeds, embedding retrieval, and LLM generation
were not rerun. The saved fragment summary was checked as archived evidence,
not re-established as a new mechanized proof of the Python pipeline.

The main source theorem is quoted directly in `coq/README.md`. It concerns the
modeled AST calculus and right-appended contexts; it must not be read as an
end-to-end proof of the separate Python regex-based implementation.
