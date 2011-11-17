Require Import List.
Require Import String.
Require Import Peano_dec.
Require Import Compare_dec.

Definition var := nat.
Definition pcpl := string.

Inductive principal : Type :=
| Var_p : var -> principal
| Pcpl_p : pcpl -> principal.

Definition principal_dec : forall a b : principal, {a=b} + {a <> b}.
generalize string_dec ;
generalize eq_nat_dec ;
decide equality.
Defined.

Inductive formula : Type :=
| Pred_f : string -> principal -> formula
| Impl_f : formula -> formula -> formula
| Signed_f : principal -> formula -> formula
| Says_f : principal -> formula -> formula
| Confirms_f : principal -> formula -> formula
| Abs_f : formula -> formula.

Definition formula_dec : forall a b : formula, {a=b} + {a <> b}.
generalize principal_dec ;
generalize string_dec ;
decide equality.
Defined.

Definition context := list formula.

Fixpoint member (f:formula) (C:context) : Prop := 
  match C with 
    | nil => False
    | p::rest => if formula_dec f p then True else member f rest
  end.

Fixpoint subst (a:pcpl) (f:formula) (n:var) : formula :=
  match f with
    | Pred_f s (Var_p v) => if eq_nat_dec v n 
                              then Pred_f s (Pcpl_p a)
                              else if gt_dec v n
                                then Pred_f s (Var_p (v -1))
                                else Pred_f s (Var_p v)
    | Pred_f s (Pcpl_p p) => Pred_f s (Pcpl_p p)
    | Impl_f f1 f2 => Impl_f (subst a f1 n) (subst a f2 n)
    | Signed_f (Var_p v) f => if eq_nat_dec v n
                                then Signed_f (Pcpl_p a) (subst a f n)
                                else if gt_dec v n
                                  then Signed_f (Var_p (v-1)) (subst a f n)
                                  else Signed_f (Var_p v) (subst a f n)
    | Signed_f (Pcpl_p p) f => Signed_f (Pcpl_p p) (subst a f n)
    | Says_f (Var_p v) f => if eq_nat_dec v n
                             then Says_f (Pcpl_p a) (subst a f n)
                             else if gt_dec v n
                               then Says_f (Var_p (v-1)) (subst a f n)
                               else Says_f (Var_p v) (subst a f n)
    | Says_f (Pcpl_p p) f => Says_f (Pcpl_p p) (subst a f n)
    | Confirms_f (Var_p v) f => if eq_nat_dec v n
                                  then Confirms_f (Pcpl_p a) (subst a f n)
                                  else if gt_dec v n
                                    then Confirms_f (Var_p (v-1)) (subst a f n)
                                    else Confirms_f (Var_p v) (subst a f n)
    | Confirms_f (Pcpl_p p) f => Confirms_f (Pcpl_p p) (subst a f n)
    | Abs_f f => Abs_f (subst a f (n+1))
  end.

Reserved Notation "c '|--' g" (at level 70).

Inductive entails : context -> formula -> Prop :=
| Init_e : forall C f, member f C -> C |-- f
| Tauto_e : forall C f, C |-- f -> 
                forall a, C |-- Says_f a f
| Weaken_e : forall C f1 f2, f1::C |-- f2 -> 
                                   C |-- Impl_f f1 f2
| Impl_e : forall C f1 f2 f3, C |-- f1 -> 
                                  f2::C |-- f3 ->
                                    (Impl_f f1 f2)::C |-- f3
| Signed_e : forall C a f1 f2, f1::C |-- Says_f a f2 -> 
                                   (Signed_f a f1)::C |-- Says_f a f2
| Confirms_e : forall C a f1 f2, f1::C |-- Says_f a f2 -> 
                                     (Confirms_f a f1)::C |-- Says_f a f2
| Says_e : forall C a f1 f2, f1::C |-- Says_f a f2 ->
                                 (Says_f a f1)::C |-- Says_f a f2
| Spec_e : forall C p f1 f2 a, (subst p f1 0)::C |-- Says_f a f2 ->
                                 (Abs_f f1)::C |-- Says_f a f2
where "C '|--' F" := (entails C F).

Definition delegate a b p := Signed_f (Pcpl_p a) (Abs_f (Impl_f (Says_f (Pcpl_p b) (Pred_f p (Var_p 0))) (Pred_f p (Var_p 0)))).

Open Local Scope string_scope.

Ltac prove_auth := 
  match goal with
    | [ |- (Abs_f _)::_ |-- Says_f _ _ ] => idtac
    | [ |- (Says_f ?a _)::_ |-- Says_f ?a _ ] => eapply Says_e
    | [ |- (Confirms_f ?a _)::_ |-- Says_f ?a _ ] => eapply Confirms_e
    | [ |- (Signed_f ?a _)::_ |-- Says_f ?a _ ] => eapply Signed_e
    | [ |- (Impl_f _ _)::_ |-- _ ] => eapply Impl_e
    | [ |- _ |-- Impl_f _ _ ] => eapply Weaken_e
    | [ |- _ |-- Says_f _ _ ] => eapply Tauto_e
    | [ |- _ |-- _] => try (econstructor ; simpl ; auto)
  end.

Ltac spec_auth p := eapply (Spec_e _ p _ _ _) ; simpl.

Lemma test : (delegate "a" "b" "ok")::(Signed_f (Pcpl_p "b") (Pred_f "ok" (Pcpl_p "c")))::nil |-- Says_f (Pcpl_p "a") (Pred_f "ok" (Pcpl_p "c")).
Proof.
  Show.
  unfold delegate ; repeat prove_auth; spec_auth "c" ; repeat prove_auth.
Qed.

Lemma says : Signed_f (Pcpl_p "a") (Pred_f "p" (Pcpl_p "a"))::nil  |-- Says_f (Pcpl_p "a") (Pred_f "p" (Pcpl_p "a")).
Proof.
 Show.
 apply Signed_e.
 apply Tauto_e.
 apply Init_e.
 simpl. auto.
Qed.

(** Define a data structure for proofs *)
Inductive proof : Set :=
 | Signed_r : formula -> proof (* formula = Signed_f f *)
 | Confirms_r : formula -> proof (* formula = Confirms_f f *)
 | Tauto_r : formula -> proof -> proof (* formula = Says_f a f, proof of f *) 
(* | Weaken_r : formula -> proof -> proof *)
 | Impl_r : formula -> proof -> proof -> proof -> proof (* formula = f3, proof of f1, f1->f2, f2->f3 *)
 | Says_Confirms_r : formula -> proof -> proof -> proof (* formula = Says_f a f2, proof of Confirms_f a f1, f1->Says_f a f2 *) 
 | Says_Signed_r : formula -> proof -> proof -> proof (* formula = Says_f a f2, proof of Signed_f a f1, f1->Says_f a f2 *) 
 | Says_Says_r : formula -> proof -> proof -> proof (* formula = Says_f a f2, proof of Says_f a f1, f1->Says_f a f2 *) 
 | Says_Spec_r : formula -> pcpl -> proof -> proof -> proof. (* formula = Says_f a f2, principal = p, proof of Abs_f f1, subst p f1 0 -> Says_f a f2 *)

(** Define a proof checking function (Fixpoint check : formula -> proof -> Prop) *)

Definition proof_goal p : formula :=
match p with
  | Signed_r f => f
  | Confirms_r f => f
  | Tauto_r f _ => f
  | Impl_r f _ _ _ => f
  | Says_Confirms_r f _ _ => f 
  | Says_Signed_r f _ _ => f
  | Says_Says_r f _ _ => f
  | Says_Spec_r f _ _ _ => f
end.

Fixpoint check (g:formula) (p:proof) : Prop :=
  match p with
    | Signed_r f => match f with
                      | Signed_f _ _ => if formula_dec f g then True else False
                      | _ => False
                    end
    | Confirms_r f => match f with
                      | Confirms_f _ _ => if formula_dec f g then True else False
                      | _ => False
                      end
    | Tauto_r f p1 => match f with
                        | Says_f _ f2 => if formula_dec f g then check f2 p1 else False
                        | _ => False
                      end
    | Impl_r f p1 p2 p3 => match proof_goal p2 with
                             | Impl_f f1 f2 => check f1 p1 /\ check (Impl_f f1 f2) p2 /\ check (Impl_f f2 f) p3
                             | _ => False
                           end
    | Says_Confirms_r f p1 p2 => match f with
                                   | Says_f a f2 => match proof_goal p1 with
                                                      | Confirms_f a f1 => check (Confirms_f a f1) p1 /\ check (Impl_f f1 f) p2
                                                      | _ => False
                                                    end
                                   | _ => False
                                 end
    | Says_Signed_r f p1 p2 => match f with
                                   | Says_f a f2 => match proof_goal p1 with
                                                      | Signed_f a f1 => check (Signed_f a f1) p1 /\ check (Impl_f f1 f) p2
                                                      | _ => False
                                                    end
                                   | _ => False
                                 end
    | Says_Says_r f p1 p2 =>  match f with
                                   | Says_f a f2 => match proof_goal p1 with
                                                      | Says_f a f1 => check (Says_f a f1) p1 /\ check (Impl_f f1 f) p2
                                                      | _ => False
                                                    end
                                   | _ => False
                                 end
    | Says_Spec_r f theP p1 p2 => match f with
                                    | Says_f a f2 => match proof_goal p1 with
                                                       | Abs_f f1 => check (Abs_f f1) p1 /\ check (Impl_f (subst theP f1 0) f) p2
                                                       | _ => False
                                                     end
                                    | _ => False
                                  end
  end.

Fixpoint axioms (p:proof) : context :=
match p with
  | Signed_r f => f::nil
  | Confirms_r f => f::nil
  | Tauto_r f p1 => axioms p1
  | Impl_r f p1 p2 p3 => List.app (axioms p1) (List.app (axioms p2) (axioms p3))
  | Says_Confirms_r f p1 p2 => List.app (axioms p1) (axioms p2) 
  | Says_Signed_r f p1 p2 => List.app (axioms p1) (axioms p2)
  | Says_Says_r f p1 p2 => List.app (axioms p1) (axioms p2)
  | Says_Spec_r f _ p1 p2 => List.app (axioms p1) (axioms p2)
end.

(** Prove that check f p -> (all signed or confirmed things) |- f *)

Lemma foo : forall f1 f2, (if formula_dec f1 f2 then True else False) = (if formula_dec f2 f1 then True else False). 
Proof.
  intros ; destruct formula_dec ; destruct formula_dec ; simpl ; congruence.
Qed.  

Theorem checker_correct : forall f p, check f p -> axioms p |-- f.
Proof.
  intros.
  induction p ; try (simpl in * ; destruct f0 ; try (exfalso ; auto ; fail) ; prove_auth ; try (rewrite foo ; auto) ; fail).
  assert (axioms (Tauto_r f0 p) = axioms p).
  simpl ; auto.
  rewrite H0.
  simpl in H.
  destruct f0 ; try (exfalso ; auto ; fail).
  destruct formula_dec.
  rewrite e in H0.
Admitted.