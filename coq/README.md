# SAPSE-Coq: Mechanized Soundness of an AST-Based Sanitizer

This artifact provides a minimal, compiling Coq development of the SAPSE sanitizer with
explicit side conditions and a composite theorem `R_AST_sound` suitable for FM 2026 review.

## Layout

```
_CoqProject
Makefile
theories/
  Syntax.v      (* identifiers, types, terms, size *)
  Typing.v      (* contexts, disjointness, typing, tailored weakening *)
  Semantics.v   (* partial ground evaluation + Prop interpretation *)
  Sanitizer.v   (* R_req, R_bind, R_eq; and key lemmas *)
  Soundness.v   (* composite theorem R_AST_sound *)
```

## Build (Coq 8.19)

```bash
make -j
```

No `Admitted.` are present.

## What is proved

1. **Import-only, no-rebinding**: `disjoint_ctx : ctx -> ctx -> Prop` and lemma
   `req_includes_right : disjoint_ctx Γ_ext Γ -> Γ ⊆ R_req Γ_ext Γ`.

2. **Tailored weakening for R_req**: `weakening_req` lifts typings from `Γ` to `R_req Γ_ext Γ`.

3. **Freshness preserved**: `fresh_preserved_by_req`.

4. **Binder normalization typing**: `WellFormedU` and `R_bind_typing` (here `R_bind` is identity).

5. **Equality canonicalization semantics**: `R_eq_sem : ∀ρ, ⟦t⟧ρ ↔ ⟦R_eq t⟧ρ` (and `R_eq_typing`).

6. **Composite theorem**:

```coq
Theorem R_AST_sound :
  forall Γ Γ_ext t τ,
    disjoint_ctx Γ_ext Γ ->
    WellFormedU t ->
    Γ ⊢ t ∈ τ ->
  let (Γ', t') := R_AST Γ_ext Γ t in
    Γ ⊆ Γ' /\
    Γ' ⊢ t' ∈ τ /\
    forall ρ, ⟦t⟧ρ <-> ⟦t'⟧ρ.
```

## Notes

- **Abstention policy**. The sanitizer function `R_AST` is total. The soundness theorem is
  stated for admissible cases (premises `disjoint_ctx`, `WellFormedU`, and typing).

- **Universe consistency**. Import-only extensions do not rebind any key from `Γ`.

- **Capture avoidance**. Equality canonicalization only swaps arguments (no new binders).
