# Third-party notices

The [MIT License](LICENSE) applies to this project's code and documentation to
the extent the authors hold the relevant rights. It does not replace upstream
terms for dependencies, original proof corpora, source-derived text, or model
weights. Dependency packages and models should be obtained with their own
licenses and notices.

| Component or source | Upstream | License information |
| --- | --- | --- |
| CompCert | https://compcert.org/ and https://github.com/AbsInt/CompCert | INRIA Non-Commercial License for source components covered by that license; consult the upstream tree for component-specific terms |
| Coq/Rocq standard library | https://github.com/rocq-prover/stdlib | LGPL-2.1; consult the version used |
| coq-ext-lib | https://github.com/coq-community/coq-ext-lib | MIT |
| FAISS | https://github.com/facebookresearch/faiss | MIT |
| Transformers | https://github.com/huggingface/transformers | Apache-2.0 |
| Sentence Transformers | https://github.com/UKPLab/sentence-transformers | Apache-2.0 |
| PyTorch | https://github.com/pytorch/pytorch | BSD-style license and bundled third-party notices |

The 2,000-item input identifies CompCert source lemmas and contains generated
Coq drafts and natural-language proof traces. The corpus index and raw corpus
source trees are not included in this release. See [data/README.md](data/README.md)
for the supplied fields and provenance. A generated or extracted representation
does not by itself establish permission to redistribute every source-derived
field; downstream users must retain applicable source attribution and license
terms.

The bundled [CompCert license notice](licenses/CompCert-LICENSE) is a verbatim
copy of the upstream notice at commit `2685140bf72c959446981fb99b5e44a8975021bc`
([source](https://raw.githubusercontent.com/AbsInt/CompCert/2685140bf72c959446981fb99b5e44a8975021bc/LICENSE)). It includes the INRIA
Non-Commercial License and component-specific alternatives. Its redistribution
clause requires the same terms for covered derivatives, and its publication
credit clause requires acknowledgment of the INRIA CompCert research project.
This notice identifies the applicable upstream terms; the original corpus source
revision is not recorded in the released benchmark metadata.
