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

Print sumor.

Definition subst_p (p:pcpl) (prin: principal) (n:var) : principal :=
  match prin with 
    | Pcpl_p _ => prin
    | Var_p v =>
      match lt_eq_lt_dec v n with
       | inleft (left _ ) => Var_p v
       | inleft (right _ ) => Pcpl_p p
       | inright _ => Var_p (v-1)
      end
  end.

Fixpoint subst (a:pcpl) (f:formula) (n:var) : formula :=
  match f with
    | Pred_f s v => Pred_f s (subst_p a v n) (* TODO fix the rest *)
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

Definition env := list (option pcpl).

Reserved Notation "c '|--' g" (at level 70).

Inductive entails : context -> formula -> Prop :=
| Init_e : forall C f, f::C |-- f
| Tauto_e : forall C f, C |-- f -> 
                forall a, C |-- Says_f a f
| Weaken_Impl_e : forall C f1 f2, f1::C |-- f2 -> 
                                   C |-- Impl_f f1 f2
| Impl_e : forall C f1 f2 f3, C |-- f1 -> 
                                  f2::C |-- f3 ->
                                    (Impl_f f1 f2)::C |-- f3
| Signed_e : forall C a f1 f2, f1::C |-- Says_f a f2 -> 
                                   (Signed_f a f1)::C |-- Says_f a f2
| Signed_Assump_e : forall C a f, C |-- Signed_f a f
| Confirms_e : forall C a f1 f2, f1::C |-- Says_f a f2 -> 
                                     (Confirms_f a f1)::C |-- Says_f a f2
| Confirms_Assump_e : forall C a f, C |-- Confirms_f a f
| Says_e : forall C a f1 f2, f1::C |-- Says_f a f2 ->
                                 (Says_f a f1)::C |-- Says_f a f2
| Spec_e : forall C p f1 f2 a, (subst p f1 0)::C |-- Says_f a f2 ->
                                 (Abs_f f1)::C |-- Says_f a f2
| Weaken_e : forall C1 f, C1 |-- f -> forall C2, incl C1 C2 -> C2 |-- f (* should prove as a lemma *)
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
    | [ |- _ |-- Impl_f _ _ ] => eapply Weaken_Impl_e
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

Definition prsubst (p:principal) (e:env) : principal :=
  match p with
    | Pcpl_p thep => p
    | Var_p v => match nth_error e v with
                   | Some (Some prl) => (Pcpl_p prl)
                   | Some (None) => p
                   | None => p
                 end
  end.

Fixpoint subst_simul (e:env) (f:formula) : formula :=
  match f with
    | Pred_f s v => Pred_f s (prsubst v e) (* TODO fix the rest *)
    | Impl_f f1 f2 => Impl_f (subst_simul e f1) (subst_simul e f2)
    | Signed_f p f => Signed_f (prsubst p e) (subst_simul e f)
    | Says_f p f => Says_f (prsubst p e) (subst_simul e f)
    | Confirms_f p f => Confirms_f (prsubst p e) (subst_simul e f) 
    | Abs_f f => Abs_f (subst_simul (None::e) f)
  end.

Fixpoint formula_comp e1 f1 e2 f2 : option (subst_simul e1 f1 = subst_simul e2 f2).
  refine (
  match f1, f2 with
    | Pred_f p1 pr1, Pred_f p2 pr2 => 
      if string_dec p1 p2 
        then let p1 := prsubst pr1 e1 in
             let p2 := prsubst pr2 e2 in
               if principal_dec p1 p2 then Some _ else None
        else None
    | Impl_f f3 f4, Impl_f f5 f6 => 
      if formula_comp e1 f3 e2 f5 then if formula_comp e1 f4 e2 f6 then Some _ else None else None
    | Signed_f pr1 f3, Signed_f pr2 f4 => 
      let p1 := prsubst pr1 e1 in
        let p2 := prsubst pr2 e2 in
          if principal_dec p1 p2 then 
            if formula_comp e1 f3 e2 f4 then Some _ else None else None
    | Says_f pr1 f3, Says_f pr2 f4 => 
      let p1 := prsubst pr1 e1 in
        let p2 := prsubst pr2 e2 in
          if principal_dec p1 p2 then 
            if formula_comp e1 f3 e2 f4 then Some _ else None else None
    | Confirms_f pr1 f3, Confirms_f pr2 f4 => 
      let p1 := prsubst pr1 e1 in
        let p2 := prsubst pr2 e2 in
          if principal_dec p1 p2 then 
            if formula_comp e1 f3 e2 f4 then Some _ else None else None
    | Abs_f f3, Abs_f f4 =>
      if formula_comp (None::e1) f3 (None::e2) f4 then Some _ else None
    | _ , _=> None
  end); clear formula_comp ; try abstract ( subst; 
  simpl; repeat match goal with 
                  | [ H : _ = _ |- _ ] => rewrite H
                end; reflexivity).
Defined.

Fixpoint axioms (e:env) (p:proof) : context :=
match p with
  | Signed_r f => (subst_simul e f)::nil
  | Confirms_r f => (subst_simul e f)::nil
  | Tauto_r f p1 => axioms e p1
  | Impl_r f p1 p2 p3 => List.app (axioms e p1) (List.app (axioms e p2) (axioms e p3))
  | Says_Confirms_r f p1 p2 => List.app (axioms e p1) (axioms e p2) 
  | Says_Signed_r f p1 p2 => List.app (axioms e p1) (axioms e p2)
  | Says_Says_r f p1 p2 => List.app (axioms e p1) (axioms e p2)
  | Says_Spec_r f a p1 p2 => List.app (axioms ((Some a)::e) p1) (axioms ((Some a)::e) p2)
end.

Definition assumps (e:env) (p:proof) : context :=
match p with
  | Signed_r f => nil
  | Confirms_r f => nil
  | Tauto_r f p1 => (subst_simul e (proof_goal p1))::nil
  | Impl_r f p1 p2 p3 => (subst_simul e (proof_goal p1))::(subst_simul e (proof_goal p2))::(subst_simul e (proof_goal p3))::nil
  | Says_Confirms_r f p1 p2 => (subst_simul e (proof_goal p1))::(subst_simul e (proof_goal p2))::nil
  | Says_Signed_r f p1 p2 => (subst_simul e (proof_goal p1))::(subst_simul e (proof_goal p2))::nil
  | Says_Says_r f p1 p2 => (subst_simul e (proof_goal p1))::(subst_simul e (proof_goal p2))::nil
  | Says_Spec_r f a p1 p2 => (subst_simul ((Some a)::e) (proof_goal p1))::(subst_simul ((Some a)::e) (proof_goal p2))::nil
end.

Fixpoint all_none (e:env) : Prop :=
  match e with
    | nil => True
    | None::e2 => all_none e2
    | _ => False
  end.

Lemma nth_foo : forall T ls n (x:T), nth_error ls n = Some x -> In x ls.
Admitted.

Lemma prsubst_nil : forall p e, all_none e -> ((prsubst p e) = p).
Proof.
  intros.
  unfold prsubst.
  destruct p ; auto.
  case_eq (nth_error e v) ; intros ; subst ; auto.
  destruct o ; auto.
  elimtype False.
  apply nth_foo in H0.
  induction e.
  auto.
  destruct H0.
  subst ; simpl in * ; congruence.
  apply IHe. simpl in H. destruct a ; auto ; exfalso ; auto.
  apply H0.
Qed.

Lemma subst_nil : forall f e, all_none e -> ((subst_simul e f) = f).
Proof.
  induction f ; intros ; simpl ; try(rewrite prsubst_nil ; auto) ;
  simpl ; auto ; try(rewrite IHf) ; auto ;
  specialize (IHf1 e H) ; specialize (IHf2 e H) ; rewrite IHf1 ; rewrite IHf2 ; auto.
Qed.

Lemma weaken : forall C f1, C |-- f1 -> forall f2, C |-- f2 -> f1::C |-- f2.
Admitted.

Lemma weaken_many : forall C1 f, (C1 |-- f) -> forall C2, (C2++C1)%list |-- f.
Admitted.

(** Proof checker - Checks the proof tree from the bottom up. *)
Fixpoint check (g:formula) (e:env) (p:proof) : option (axioms e p |-- subst_simul e g).
  refine (
    let f := proof_goal p in
  match formula_comp e g e f with
    | None => None
    | Some fg_eq =>
      match p with
        | Signed_r (Signed_f pr f1) => 
            if formula_comp e f e (Signed_f pr f1) then Some _ else None
        | Confirms_r (Confirms_f pr f1) => 
            if formula_comp e f e (Confirms_f pr f1) then Some _ else None
        | Tauto_r (Says_f pr f1) p1 => 
            if formula_comp e f e (Says_f pr f1) then if check f1 e p1 then Some _ else None else None
(*        | Impl_r f3 p1 p2 p3 => 
            if formula_comp e f e f3
              then match proof_goal p2 with
                     | Impl_f f1 f2 => if check f1 e p1
                                         then if check (Impl_f f1 f2) e p2
                                                then if check (Impl_f f2 f3) e p3 then Some _ else None
                                                else None
                                         else None
                     | _ => None
                   end
              else None*)
        | Says_Confirms_r (Says_f pr f2) p1 p2 =>
            if formula_comp e f e (Says_f pr f2)
              then match proof_goal p1 with
                     | Confirms_f pr0 f1 => if principal_dec (prsubst pr e) (prsubst pr0 e)
                                              then
                                                if check (Confirms_f pr f1) e p1
                                                  then if check (Impl_f f1 f) e p2 then Some _ else None
                                                  else None
                                              else None
                     | _ => None
                   end
              else None
        | _ => None
      end
  end) ;
  try (rewrite fg_eq in * ; rewrite _H in * ; subst ; simpl in * ; prove_auth ; auto ; fail).
  

(*
        | Confirms_r f => match f with
                            | Confirms_f _ _ => formula_comp e g e f
                            | _ => False
                          end
        | Tauto_r f p1 => match f with
                            | Says_f _ f2 => match formula_comp e g e f with 
                                               | True => check f2 e p1 
                                             end
                            | _ => False
                          end
        | Impl_r f p1 p2 p3 => match proof_goal p2 with
                                 | Impl_f f1 f2 => check f1 e p1 /\ check (Impl_f f1 f2) e p2 /\ check (Impl_f f2 f) e p3
                                 | _ => False
                               end
        | Says_Confirms_r f p1 p2 => match f with
                                       | Says_f a f2 => match proof_goal p1 with
                                                          | Confirms_f a f1 => check (Confirms_f a f1) e p1 /\ check (Impl_f f1 f) e p2
                                                          | _ => False
                                                        end
                                       | _ => False
                                     end
        | Says_Signed_r f p1 p2 => match f with
                                     | Says_f a f2 => match proof_goal p1 with
                                                        | Signed_f a f1 => check (Signed_f a f1) e p1 /\ check (Impl_f f1 f) e p2
                                                        | _ => False
                                                      end
                                     | _ => False
                                   end
        | Says_Says_r f p1 p2 =>  match f with
                                    | Says_f a f2 => match proof_goal p1 with
                                                       | Says_f a f1 => check (Says_f a f1) e p1 /\ check (Impl_f f1 f) e p2
                                                       | _ => False
                                                     end
                                    | _ => False
                                  end
        | Says_Spec_r f theP p1 p2 => match f with
                                        | Says_f a f2 => match proof_goal p1 with
                                                           | Abs_f f1 => check (Abs_f f1) e p1 /\ check (Impl_f (subst theP f1 0) f) e p2
                                                           | _ => False
                                                         end
                                        | _ => False
                                      end
      end
   end. (* The formula does not match the goal *)*)