From Stdlib Require Import String List Arith PeanoNat Bool.
From Stdlib Require Import Classes.Morphisms.
Import ListNotations.
From SAPSE Require Import Syntax Typing Semantics.

Module SAPSE_Sanitizer.
Import SAPSE_Syntax SAPSE_Typing SAPSE_Semantics.

(* ---------- Import-only context extension as right append ---------- *)

Definition R_req (Γ_ext Γ:ctx) : ctx := Γ ++ Γ_ext.

Lemma req_includes_right : forall Γ_ext Γ,
  Γ ⊆ R_req Γ_ext Γ.
Proof.
  unfold ctx_includes, R_req; intros Γ_ext Γ x A Hlk.
  apply lookup_app_preserve. exact Hlk.
Qed.

(* If x maps to A in Γ, it still maps to A in Γ ++ Δ. *)
Lemma lookup_app_left : forall (x:ident) (A:ty) Γ Δ,
  lookup x Γ = Some A -> lookup x (Γ ++ Δ) = Some A.
Proof.
  intros x A Γ Δ H. induction Γ as [| [y B] Γ IH]; simpl in *.
  - discriminate.
  - destruct (String.eqb x y) eqn:E; [assumption| now apply IH].
Qed.

(* Weakening for right-append import-only extension: no disjoint/fresh needed. *)
Lemma weakening_req : forall Γ_ext Γ t T,
  Γ ⊢ t ∈ T -> R_req Γ_ext Γ ⊢ t ∈ T.
Proof.
  unfold R_req. induction 1; simpl.
  - (* T_Var *) constructor. eapply lookup_app_left; eauto.
  - (* T_Nat *) constructor.
  - (* T_Bool *) constructor.
  - (* T_Add *) econstructor; eauto.
  - (* T_Eq *) econstructor; eauto.
  - (* T_Lam *)
    constructor.
    change ((x,A)::Γ ++ Γ_ext) with (((x,A)::Γ) ++ Γ_ext).
    now apply IHhas_type.
  - (* T_App *) econstructor; eauto.
  - (* T_Forall *)
    constructor.
    change ((x,A)::Γ ++ Γ_ext) with (((x,A)::Γ) ++ Γ_ext).
    now apply IHhas_type.
Qed.

(* ---------- Binder normalization ---------- *)

Inductive WellFormedU : term -> Prop :=
| WF_Var : forall x, WellFormedU (tVar x)
| WF_Nat : forall n, WellFormedU (tNat n)
| WF_Bool: forall b, WellFormedU (tBool b)
| WF_Add : forall a b, WellFormedU a -> WellFormedU b -> WellFormedU (tAdd a b)
| WF_Eq  : forall a b, WellFormedU a -> WellFormedU b -> WellFormedU (tEq a b)
| WF_Lam : forall x A body, WellFormedU body -> WellFormedU (tLam x A body)
| WF_App : forall a b, WellFormedU a -> WellFormedU b -> WellFormedU (tApp a b)
| WF_Forall : forall x A body, WellFormedU body -> WellFormedU (tForall x A body).

#[local] Hint Constructors WellFormedU : core.

Definition R_bind (t:term) : term := t.

Lemma R_bind_typing : forall Γ t T,
  WellFormedU t -> Γ ⊢ t ∈ T -> Γ ⊢ R_bind t ∈ T.
Proof. intros; simpl; assumption. Qed.

Lemma R_bind_sem : forall ρ t, ⟦t⟧ρ <-> ⟦R_bind t⟧ρ.
Proof. intros; unfold R_bind; tauto. Qed.

(* ---------- Equality canonicalization ---------- *)

Definition canon_eq (a b:term) : term * term :=
  if Nat.leb (term_size a) (term_size b) then (a,b) else (b,a).

(* Structural recursion: recurse on subterms before canonicalization *)
Fixpoint R_eq (t:term) : term :=
  match t with
  | tEq a b =>
      let a' := R_eq a in
      let b' := R_eq b in
      let '(c1,c2) := canon_eq a' b' in
      tEq c1 c2
  | tAdd a b        => tAdd (R_eq a) (R_eq b)
  | tApp a b        => tApp (R_eq a) (R_eq b)
  | tLam x A body   => tLam x A (R_eq body)
  | tForall x A bod => tForall x A (R_eq bod)
  | _               => t
  end.

(* Symmetry for equality semantics at the Prop level. *)
Lemma denote_eq_swap : forall ρ a b, ⟦tEq a b⟧ρ <-> ⟦tEq b a⟧ρ.
Proof.
  intros. unfold denote. rewrite eval_eq_swap. tauto.
Qed.

(* denote unfolds to a match on eval *)
Lemma denote_eval_iff : forall ρ t,
  ⟦t⟧ρ <-> match eval ρ t with Some v => asProp v | None => True end.
Proof. intros. now unfold denote. Qed.

(* Helper: R_eq preserves eval results *)
Lemma R_eq_eval_eq : forall ρ t,
  eval ρ t = eval ρ (R_eq t).
Proof.
  intros ρ t. induction t; simpl; try reflexivity.
  - (* tAdd *)
    rewrite <- IHt1, <- IHt2. reflexivity.
  - (* tEq *)
    destruct (canon_eq (R_eq t1) (R_eq t2)) as [c1 c2] eqn:Hcanon.
    unfold canon_eq in Hcanon.
    destruct (Nat.leb (term_size (R_eq t1)) (term_size (R_eq t2))) eqn:Hleb.
    + injection Hcanon as H1 H2. subst c1 c2.
      simpl. rewrite <- IHt1, <- IHt2. reflexivity.
    + injection Hcanon as H1 H2. subst c1 c2.
      rewrite eval_eq_swap. simpl. rewrite <- IHt1, <- IHt2. reflexivity.
Qed.

(* The original statement was unprovable: (⟦a⟧ρ <-> ⟦a'⟧ρ) does not imply
   that VNat values are equal, since asProp (VNat n) = True for all n.
   We strengthen to require eval equality. *)
Lemma denote_tEq_proper : forall ρ a a' b b',
  eval ρ a = eval ρ a' ->
  eval ρ b = eval ρ b' ->
  ⟦tEq a b⟧ρ <-> ⟦tEq a' b'⟧ρ.
Proof.
  intros ρ a a' b b' Ha Hb.
  unfold denote. simpl.
  rewrite Ha, Hb.
  reflexivity.
Qed.

Lemma R_eq_sem : forall ρ t, ⟦t⟧ρ <-> ⟦R_eq t⟧ρ.
Proof.
  intros ρ t; induction t; try (simpl; tauto).
  - (* tAdd *)
    simpl.
    unfold denote at 1 2; simpl.
    unfold denote in IHt1, IHt2.
    destruct (eval ρ t1) as [[n1|b1]|] eqn:E1;
    destruct (eval ρ t2) as [[n2|b2]|] eqn:E2;
    destruct (eval ρ (R_eq t1)) as [[rn1|rb1]|] eqn:RE1;
    destruct (eval ρ (R_eq t2)) as [[rn2|rb2]|] eqn:RE2;
    simpl in *; tauto.
  - (* tEq *)
    simpl.
    destruct (canon_eq (R_eq t1) (R_eq t2)) as [c1 c2] eqn:Hcanon.
    unfold canon_eq in Hcanon.
    destruct (Nat.leb (term_size (R_eq t1)) (term_size (R_eq t2))) eqn:Hleb.
    + (* c1 = R_eq t1, c2 = R_eq t2 *)
      injection Hcanon as H1 H2. subst c1 c2.
      eapply denote_tEq_proper.
      * rewrite R_eq_eval_eq. reflexivity.
      * rewrite R_eq_eval_eq. reflexivity.
    + (* c1 = R_eq t2, c2 = R_eq t1 *)
      injection Hcanon as H1 H2. subst c1 c2.
      etransitivity.
      2: { apply denote_eq_swap. }
      eapply denote_tEq_proper.
      * rewrite R_eq_eval_eq. reflexivity.
      * rewrite R_eq_eval_eq. reflexivity.
Qed.

Lemma R_eq_typing : forall Γ t T, Γ ⊢ t ∈ T -> Γ ⊢ R_eq t ∈ T.
Proof.
  induction 1; simpl.
  - (* T_Var *) constructor. assumption.
  - (* T_Nat *) constructor.
  - (* T_Bool *) constructor.
  - (* T_Add *) econstructor; eauto.
  - (* T_Eq case: canon_eq swaps but both orderings type the same *)
    remember (canon_eq (R_eq t1) (R_eq t2)) as p; destruct p as [c1 c2].
    unfold canon_eq in Heqp.
    destruct (Nat.leb (term_size (R_eq t1)) (term_size (R_eq t2))) eqn:E.
    + injection Heqp as H1 H2; subst c1 c2. econstructor; eauto.
    + injection Heqp as H1 H2; subst c1 c2. econstructor; eauto.
  - (* T_Lam *) constructor. eauto.
  - (* T_App *) econstructor; eauto.
  - (* T_Forall *) constructor. eauto.
Qed.

(* ---------- Composite sanitizer ---------- *)

Definition R_AST (Γ_ext Γ:ctx) (t:term) : (ctx * term) :=
  let Γ' := R_req Γ_ext Γ in
  let t1 := R_bind t in
  let t2 := R_eq t1 in
  (Γ', t2).

End SAPSE_Sanitizer.
