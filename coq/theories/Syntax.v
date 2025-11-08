From Stdlib Require Import String List Arith PeanoNat Bool.
Import ListNotations.

Module SAPSE_Syntax.

Definition ident := string.

Inductive ty : Type :=
| TNat | TBool | TArrow (a b : ty).

Inductive term : Type :=
| tVar   (x:ident)
| tNat   (n:nat)
| tBool  (b:bool)
| tAdd   (t1 t2:term)
| tEq    (t1 t2:term)
| tLam   (x:ident) (A:ty) (body:term)
| tApp   (t1 t2:term)
| tForall (x:ident) (A:ty) (body:term).

Fixpoint term_size (t:term) : nat :=
  match t with
  | tVar _ | tNat _ | tBool _ => 1
  | tAdd a b | tEq a b | tApp a b => 1 + term_size a + term_size b
  | tLam _ _ b | tForall _ _ b => 1 + term_size b
  end.

End SAPSE_Syntax.
