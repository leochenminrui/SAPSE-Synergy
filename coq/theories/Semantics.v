From Stdlib Require Import String List Arith PeanoNat Bool.
Import ListNotations.
From SAPSE Require Import Syntax Typing.

Module SAPSE_Semantics.
Import SAPSE_Syntax SAPSE_Typing.

Inductive val : Type :=
| VNat : nat -> val
| VBool : bool -> val.

Definition env := list (ident * val).

Fixpoint env_get (x:ident) (ρ:env) : option val :=
  match ρ with
  | [] => None
  | (y,v)::ρ' => if String.eqb x y then Some v else env_get x ρ'
  end.

Fixpoint eval (ρ:env) (t:term) : option val :=
  match t with
  | tVar x => env_get x ρ
  | tNat n => Some (VNat n)
  | tBool b => Some (VBool b)
  | tAdd a b =>
      match eval ρ a, eval ρ b with
      | Some (VNat m), Some (VNat n) => Some (VNat (m+n))
      | _, _ => None
      end
  | tEq a b =>
      match eval ρ a, eval ρ b with
      | Some (VNat m), Some (VNat n) => Some (VBool (Nat.eqb m n))
      | Some (VBool p), Some (VBool q) => Some (VBool (Bool.eqb p q))
      | _, _ => None
      end
  | tLam _ _ _ => None
  | tApp _ _ => None
  | tForall _ _ _ => None
  end.

Definition asProp (v:val) : Prop :=
  match v with
  | VBool true => True
  | VBool false => False
  | _ => True
  end.

Definition denote (ρ:env) (t:term) : Prop :=
  match eval ρ t with
  | Some v => asProp v
  | None => True
  end.

Notation "⟦ t ⟧ ρ" := (denote ρ t) (at level 50).

Lemma eval_eq_swap : forall ρ a b,
  eval ρ (tEq a b) = eval ρ (tEq b a).
Proof.
  intros ρ a b.
  simpl.
  remember (eval ρ a) as ea.
  remember (eval ρ b) as eb.
  destruct ea as [ [m|p] | ]; destruct eb as [ [n|q] | ]; simpl; try reflexivity.
  - now rewrite Nat.eqb_sym.
  - destruct p, q; reflexivity.
Qed.

End SAPSE_Semantics.
