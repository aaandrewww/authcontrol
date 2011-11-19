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
| Init_e : forall C f, member f C -> C |-- f
| Tauto_e : forall C f, C |-- f -> 
                forall a, C |-- Says_f a f
| Weaken_Impl_e : forall C f1 f2, f1::C |-- f2 -> 
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
| Weaken_e : forall f1 C f2, C |-- f2 -> f1::C |-- f2
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

(** Proof checker - Checks the proof tree from the bottom up. *)
Fixpoint check (g:formula) (e:env) (p:proof) : option (axioms e p |-- subst_simul e g).
  refine (
    let f := proof_goal p in
  match formula_comp e g e f with
    | None => None
    | Some fg_eq =>
      match p with
        | Signed_r (Signed_f pr f1) => if formula_comp e f e (Signed_f pr f1) then Some _ else None
        | Confirms_r (Confirms_f pr f1) => if formula_comp e f e (Confirms_f pr f1) then Some _ else None
        | Tauto_r (Says_f pr f1) p1 => if formula_comp e f e (Says_f pr f1) then if check f1 e p1 then Some _ else None else None
        | Impl_r f3 p1 p2 p3 => if formula_comp e f e f3
                                  then match proof_goal p2 with
                                         | Impl_f f1 f2 => if check f1 e p1
                                                             then if check (Impl_f f1 f2) e p2
                                                                    then if check (Impl_f f2 f3) e p3 then Some _ else None
                                                                    else None
                                                             else None
                                         | _ => None
                                       end
                                  else None
        | _ => None
      end
  end) ;
  simpl ; rewrite fg_eq ; rewrite _H ; try(simpl ; apply Init_e ; unfold member ; destruct formula_dec ; auto ; fail).
  simpl ; apply Tauto_e ; auto.
  simpl in *. 

Lemma weaken_ctxt : forall f1 f2 C1 C2, C1 |-- f1 -> In f2 C1 -> In f2 C2 -> C2 |-- f1.
Admitted.

Lemma weaken_ctxt_app : forall f1 C1 C2, C1 |-- f1 -> (C1++C2)%list |-- f1.
Admitted.

Lemma app_impl : forall ax1 ax2 f1 f2, ax1 |-- Impl_f f1 f2 -> ax2 |-- f1 -> List.app ax1 ax2 |-- f2.
Proof.
  intros.
  assert ((ax1 ++ ax2)%list |-- Impl_f f1 f2).
  apply weaken_ctxt_app ; auto.
  assert ((ax1 ++ ax2)%list |-- f1).
  apply weaken_ctxt_app ; auto.


Lemma rep_ax : forall f1 f2 f3 C, f1::C |-- f2 -> f3::nil |-- f1 -> f3::C |-- f2.
Proof.
  intros.
  
  
  
  assert (f3::C |-- f1).
  eapply weaken_ctxt ; auto.
  clear H0.
  apply (Impl_e 

Show.
  

  simpl in *.  induction p1. induction p2. induction p3. simpl in *.
  apply Weaken_e in _H0.
  apply Weaken_e in _H1.

  Show.
Defined.


rewrite subst_nil in fg_eq ; rewrite subst_nil in fg_eq.
  rewrite fg_eq.
  

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

(*Lemma foo : forall f1 f2, (if formula_dec f1 f2 then True else False) = (if formula_dec f2 f1 then True else False). 
Proof.
  intros ; destruct formula_dec ; destruct formula_dec ; simpl ; congruence.
Qed.  

Theorem checker_correct : forall f e p, check f e p -> axioms p |-- f.
Proof.
  intros.
  induction p.
  simpl in *.
  destruct f0 ; try (exfalso ; auto ; fail).
  
  

  induction p ; try (simpl in * ; destruct f0 ; try (exfalso ; auto ; fail) ; prove_auth ; try (rewrite foo ; auto) ; fail).
  assert (axioms (Tauto_r f0 p) = axioms p).
  simpl ; auto.
  rewrite H0.
  simpl in H.
  destruct f0 ; try (exfalso ; auto ; fail).
  destruct formula_dec.
  rewrite e in H0.
Admitted.*)