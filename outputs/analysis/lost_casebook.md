# Lost Lemma Casebook

Sampled 10 diverse examples from 96 lost successes.

---

## Example 1: CompCert:Tailcallproof:transf_instr_lookup

**Category**: Misc  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (94.6ms)
- **SAPSE-Fast**: Failed (90.8ms)
- **SAPSE-Synergy**: Failed (76.2ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Lists.List. Import ListNotations.

Lemma map_compose : forall (A B C : Type) (f : B -> C) (g : A -> B) (l : list A), map f (map g l) = map (fun x => f (g x)) l.
Proof.
  intros A B C f g l. induction l; simpl; [reflexivity|].
  rewrite IHl. reflexivity.
Qed.
```

---

## Example 2: CompCert:SelectOpproof:eval_notint

**Category**: Arithmetic  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (244.2ms)
- **SAPSE-Fast**: Failed (156.1ms)
- **SAPSE-Synergy**: Failed (169.2ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Arith.Arith.
Lemma notint_sound : forall (v : nat), v = v.
Proof. auto. Qed.
```

---

## Example 3: CompCert:SplitLongproof:eval_addl

**Category**: Arithmetic  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (116.5ms)
- **SAPSE-Fast**: Failed (79.4ms)
- **SAPSE-Synergy**: Failed (76.0ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Lists.List. Import ListNotations.

Lemma map_cons_template : forall (A B : Type) (f : A -> B) (x : A) (l : list A), map f (x :: l) = f x :: map f l.
Proof. reflexivity. Qed.
```

---

## Example 4: CompCert:SplitLongproof:eval_negl

**Category**: Boolean  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (116.8ms)
- **SAPSE-Fast**: Failed (77.0ms)
- **SAPSE-Synergy**: Failed (76.0ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Lists.List. Import ListNotations.

Lemma unary_constructor_sound_template : forall (A B : Type) (f : A -> B) (l : list A) (P : B -> Prop),
  (forall x, In x l -> P (f x)) -> Forall P (map f l).
Proof.
  intros A B f l P H.
  apply Forall_forall.
  intros b Hin.
  apply in_map_iff 
```

---

## Example 5: CompCert:Op:eval_shift_stack_operation

**Category**: Misc  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (133.7ms)
- **SAPSE-Fast**: Failed (73.0ms)
- **SAPSE-Synergy**: Failed (76.1ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Arith.PeanoNat.
Lemma add_zero_l : forall (x : nat), 0 + x = x.
Proof. apply Nat.add_0_l. Qed.
```

---

## Example 6: CompCert:Cminortyping:wt_initial_state

**Category**: Boolean  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (125.4ms)
- **SAPSE-Fast**: Failed (157.6ms)
- **SAPSE-Synergy**: Failed (156.5ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Lists.List.

Lemma initial_state_wt_state : forall (p : Type) (S : Type) (initial_state : p -> S -> Prop) (wt_state : S -> Prop),
  (forall (p0 : p) (S0 : S), initial_state p0 S0 -> wt_state S0) ->
  forall (p0 : p) (S0 : S), initial_state p0 S0 -> wt_state S0.
Proof.
  intros p S
```

---

## Example 7: CompCert:Bounds:record_reg_ok

**Category**: Boolean  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (150.5ms)
- **SAPSE-Fast**: Failed (76.8ms)
- **SAPSE-Synergy**: Failed (76.7ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Lists.List. Import ListNotations.

Lemma forallb_true_iff : forall (A : Type) (f : A -> bool) (l : list A), 
  forallb f l = true <-> (forall x, In x l -> f x = true).
Proof.
  induction l; simpl; split; intros.
  - contradiction.
  - reflexivity.
  - destruct (f a) eqn:?; try dis
```

---

## Example 8: CompCert:Asmgenproof:transf_initial_states

**Category**: Misc  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (137.3ms)
- **SAPSE-Fast**: Failed (75.6ms)
- **SAPSE-Synergy**: Failed (81.3ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Lists.List. Import ListNotations.

Lemma mach_step_transf_partial : forall (A B : Type) (TRANSF : A -> option B) (st1 st2 : A),
  (exists f, TRANSF st1 = Some f /\ TRANSF st2 = Some f) -> 
  (exists st1' st2', TRANSF st1 = Some st1' /\ TRANSF st2 = Some st2').
Proof.
  intros A B 
```

---

## Example 9: CompCert:ValueDomain:hiword_sound

**Category**: Boolean  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (108.9ms)
- **SAPSE-Fast**: Failed (73.6ms)
- **SAPSE-Synergy**: Failed (74.3ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Arith.PeanoNat.
Lemma step_vmatch : forall (v : nat) (x : nat), v <= x -> v <= S x.
Proof. intros v x H. apply Nat.le_trans with (m := x); [assumption | apply Nat.le_succ_diag_r]. Qed.
```

---

## Example 10: CompCert:RTLtyping:wt_stackframes_change_sig

**Category**: Misc  
**Complexity**: shallow  

### Status Summary

- **Baseline-RAG**: Verified (95.0ms)
- **SAPSE-Fast**: Failed (80.2ms)
- **SAPSE-Synergy**: Failed (75.8ms)

### Failure Modes

- **Fast**: OTHER
- **Synergy**: OTHER

### Error Messages

### Lemma Statement (first 300 chars)

```coq
Require Import Coq.Lists.List. Import ListNotations.

Lemma step_transition : forall (s sg1 sg2 : nat), sg1 = sg2 -> s + sg1 = s + sg2.
Proof. intros s sg1 sg2 H. rewrite H. reflexivity. Qed.
```

---

