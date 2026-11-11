# Benchmark inputs and corpus provenance

## Fixed-draft evaluation

`input/synergy_rag_2k.jsonl` contains 2,000 pre-generated Coq drafts, all identified
by a `CompCert:module:lemma` source ID. Each record includes `draft`, a
natural-language proof trace in `nl_proof`, `retrieved_count`, and generation
metadata. The evaluation runner consumes the fixed draft text, not the source
corpora or a retrieval index. These IDs describe provenance; generated drafts are
not interchangeable with the original CompCert theorem statements.

`samples/coq_lemmas.jsonl` and `samples/nl_proofs.jsonl` contain 20 small lemma
examples and five natural-language examples for library demonstrations/tests.
The exact distributed input bytes are recorded in `SHA256SUMS`.

Source-derived statements and proof traces retain any applicable upstream terms.
The project's MIT code license does not grant additional rights to the CompCert
sources or automatically relicense derived text. Consult the
[third-party notices](../THIRD_PARTY_NOTICES.md) and the original source licenses
before redistributing source-derived material.

## Retrieval on your own corpus

The fixed-draft benchmark does not need a FAISS index. This release therefore
does not distribute the historical corpus index or its pickle metadata. The
retrieval library accepts vectors and metadata that you build from inputs you
are authorized to use:

```python
import numpy as np
from sapse.retrieval import VectorIndex, SemanticSearcher

index = VectorIndex(dimension=2)
index.add_vectors(
    np.array([[1.0, 0.0], [0.0, 1.0]], dtype=np.float32),
    [{"id": "example-1", "text": "Lemma example : True."},
     {"id": "example-2", "text": "Lemma example2 : 0 = 0."}],
)
index.save("my_lemmas.faiss")
```

Install the optional backends with `python -m pip install -r
python/requirements.txt` and set `PYTHONPATH=python` when using these modules
from the repository root. The example only demonstrates the index API with
two manually supplied vectors; it does not rebuild the paper's embedding index.
For semantic retrieval, encode your own corpus and queries consistently using
an appropriate embedding model, retaining that model's identity and license.
The repository does not include the original corpus-extraction pipeline or
immutable source revisions needed to reconstruct the historical index.
