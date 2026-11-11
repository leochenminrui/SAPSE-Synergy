# Mechanized AST sanitizer

This directory contains five Rocq theories: `Syntax.v`, `Typing.v`,
`Semantics.v`, `Sanitizer.v`, and `Soundness.v`. The paper used Rocq 9.1.0;
the release sources have also been compiled with Rocq 9.1.1.

## Build

With `coqc` and `coq_makefile` on `PATH`, run from the repository root:

```bash
make -C coq
```

The Makefile generates a toolchain-specific `Makefile.coq` locally. Build
products are not distributed. To force a clean compilation:

```bash
make -C coq clean
make -C coq
```

## Main theorem

`theories/Soundness.v` states the following theorem for the modeled calculus:

```coq
Theorem R_AST_sound :
  forall Γ Γ_ext t τ,
    WellFormedU t ->
    Γ ⊢ t ∈ τ ->
  let (Γ', t') := R_AST Γ_ext Γ t in
    Γ ⊆ Γ' /\
    Γ' ⊢ t' ∈ τ /\
    forall ρ, ⟦t⟧ρ <-> ⟦t'⟧ρ.
```

`R_req` appends `Γ_ext` on the right of `Γ`; first-match lookup preserves
existing bindings. The current theorem therefore needs no disjointness premise.
`R_bind` is the identity. `R_eq` recursively canonicalizes equality arguments
by term size. The development proves preservation of typing and denotational
logical equivalence for well-formed, well-typed terms in this calculus.

The Python sanitizer is a separate implementation over Coq text, with additional
heuristic passes and guards. It is not extracted from these definitions. Building
these theories verifies the abstract core, not the entire retrieval, generation,
Python preprocessing, or natural-language alignment pipeline.
