Require Import String.
Require Import List.

Definition var := string.
Definition principal := string.

Inductive formula : Type :=
| Pred_f : string -> var -> formula
| Impl_f : formula -> formula -> formula
| Signed_f : principal -> formula -> formula
| Says_f : principal -> formula -> formula
| Confirms_f : principal -> formula -> formula.

Definition formula_dec : forall a b : formula, {a=b} + {a <> b}.
generalize string_dec.
decide equality.
Defined.

Definition context := list formula.

Fixpoint member (f:formula) (C:context) : Prop := 
  match C with 
    | nil => False
    | p::rest => if formula_dec f p then True else member f rest
  end.

Reserved Notation "c '|-' g" (at level 70).

Inductive entails : context -> formula -> Prop :=
| Init_e : forall C f, member f C -> C |- f
| Tauto_e : forall C f, C |- f -> forall a, C |- Says_f a f
| Weaken_e : forall C f1 f2, f1::C |- f2 -> C |- Impl_f f1 f2
| Impl_e : forall C f1 f2 f3, C |- f1 -> f2::C |- f3 -> (Impl_f f1 f2)::C |- f3
| Signed_e : forall C a f1 f2, f1::C |- Says_f a f2 -> (Signed_f a f1)::C |- Says_f a f2
| Confirms_e : forall C a f1 f2, f1::C |- Says_f a f2 -> (Confirms_f a f1)::C |- Says_f a f2
| Says_e : forall C a f1 f2, f1::C |- Says_f a f2 -> (Says_f a f1)::C |- Says_f a f2
where "C '|-' F" := (entails C F).

(** Define a data structure for proofs *)

(** Define a proof checking function (Fixpoint check : formula -> proof -> Prop) *)

(** Prove that check f p -> nil |- f *)