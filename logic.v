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

Definition subst_p (prin: principal) (n:var) (p:pcpl) : principal :=
  match prin with 
    | Pcpl_p _ => prin
    | Var_p v =>
      match lt_eq_lt_dec v n with
       | inleft (left _ ) => Var_p v
       | inleft (right _ ) => Pcpl_p p
       | inright _ => Var_p (v-1)
      end
  end.

Fixpoint subst (f:formula) (n:var) (a:pcpl) : formula :=
  match f with
    | Pred_f s v => Pred_f s (subst_p v n a) (* TODO fix the rest *)
    | Impl_f f1 f2 => Impl_f (subst f1 n a) (subst f2 n a)
    | Says_f v f => Says_f (subst_p v n a) (subst f n a)
    | Confirms_f v f => Confirms_f (subst_p v n a) (subst f n a)
    | Signed_f v f => Signed_f (subst_p v n a) (subst f n a)
    | Abs_f f => Abs_f (subst f (n+1) a)
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
| Confirms_e : forall C a f1 f2, f1::C |-- Says_f a f2 -> 
                                     (Confirms_f a f1)::C |-- Says_f a f2
| Says_e : forall C a f1 f2, f1::C |-- Says_f a f2 ->
                                 (Says_f a f1)::C |-- Says_f a f2
| Spec_e : forall C p f1 f2 a, (subst f1 0 p)::C |-- Says_f a f2 ->
                                 (Abs_f f1)::C |-- Says_f a f2
| Weaken_e : forall C1 C2 f, C1 |-- f -> incl C1 C2 -> C2 |-- f (* should prove as a lemma? *)
where "C '|--' F" := (entails C F).

(** The main lemma *)
Axiom cut_elimination : forall C f1 f2, C |-- f1 -> f1::C |-- f2 -> C |-- f2.

(* Could be improved a lot... *)
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

Fixpoint subst_simul (f:formula) (e:env) : formula :=
  match f with
    | Pred_f s v => Pred_f s (prsubst v e) (* TODO fix the rest *)
    | Impl_f f1 f2 => Impl_f (subst_simul f1 e) (subst_simul f2 e)
    | Signed_f p f => Signed_f (prsubst p e) (subst_simul f e)
    | Says_f p f => Says_f (prsubst p e) (subst_simul f e)
    | Confirms_f p f => Confirms_f (prsubst p e) (subst_simul f e) 
    | Abs_f f => Abs_f (subst_simul f (None::e))
  end.

Fixpoint formula_comp f1 e1 f2 e2 : option (subst_simul f1 e1 = subst_simul f2 e2).
  refine (
  match f1, f2 with
    | Pred_f p1 pr1, Pred_f p2 pr2 => 
      if string_dec p1 p2 
        then let p1 := prsubst pr1 e1 in
             let p2 := prsubst pr2 e2 in
               if principal_dec p1 p2 then Some _ else None
        else None
    | Impl_f f3 f4, Impl_f f5 f6 => 
      if formula_comp f3 e1 f5 e2 then if formula_comp f4 e1 f6 e2 then Some _ else None else None
    | Signed_f pr1 f3, Signed_f pr2 f4 => 
      let p1 := prsubst pr1 e1 in
        let p2 := prsubst pr2 e2 in
          if principal_dec p1 p2 then 
            if formula_comp f3 e1 f4 e2 then Some _ else None else None
    | Says_f pr1 f3, Says_f pr2 f4 => 
      let p1 := prsubst pr1 e1 in
        let p2 := prsubst pr2 e2 in
          if principal_dec p1 p2 then 
            if formula_comp f3 e1 f4 e2 then Some _ else None else None
    | Confirms_f pr1 f3, Confirms_f pr2 f4 => 
      let p1 := prsubst pr1 e1 in
        let p2 := prsubst pr2 e2 in
          if principal_dec p1 p2 then 
            if formula_comp f3 e1 f4 e2 then Some _ else None else None
    | Abs_f f3, Abs_f f4 =>
      if formula_comp f3 (None::e1) f4 (None::e2) then Some _ else None
    | _ , _=> None
  end); clear formula_comp ; try abstract ( subst; 
  simpl; repeat match goal with 
                  | [ H : _ = _ |- _ ] => rewrite H
                end; reflexivity).
Defined.

Fixpoint axioms (p:proof) (e:env) : context :=
match p with
  | Signed_r f => (subst_simul f e)::nil
  | Confirms_r f => (subst_simul f e)::nil
  | Tauto_r f p1 => axioms p1 e
  | Impl_r f p1 p2 p3 => List.app (axioms p1 e) (List.app (axioms p2 e) (axioms p3 e))
  | Says_Confirms_r f p1 p2 => List.app (axioms p1 e) (axioms p2 e) 
  | Says_Signed_r f p1 p2 => List.app (axioms p1 e) (axioms p2 e)
  | Says_Says_r f p1 p2 => List.app (axioms p1 e) (axioms p2 e)
  | Says_Spec_r f a p1 p2 => List.app (axioms p1 e) (axioms p2 e)
end.

Lemma subst_p_prsubst : forall p1 p2 e, (subst_p (prsubst p2 (None::e)) 0 p1) = (prsubst p2 ((Some p1)::e)).
Admitted.

Lemma subst_subst_simul : forall p e f, subst (subst_simul f (None :: e)) 0 p = subst_simul f (Some p :: e).
Admitted.

Ltac incl_apps := 
  match goal with
    | [ |- incl ?C1 (_ ++ _ ++ ?C1) ] => apply incl_appr
    | [ |- incl ?C1 (_ ++ ?C1 ++ _) ] => apply incl_appr
    | [ |- incl ?C1 (?C1 ++ _ ++ _) ] => apply incl_appl
    | [ |- incl ?C1 (?C1 ++ _) ] => apply incl_appl
    | [ |- incl ?C1 (_ ++ ?C1) ] => apply incl_appr
    | [ |- incl ?C1 ?C1 ] => apply incl_refl
    | [ |- incl ?C1 (_::?C1)] => apply incl_tl
    | [ |- incl ?C1 (_::?C1 ++ _)] => apply incl_tl
    | [ |- incl ?C1 (_::_ ++ ?C1)] => apply incl_tl
    | [ |- ?H ] => idtac H 
  end.
 
(** Proof checker - Checks the proof tree from the bottom up. *)
Fixpoint check (g:formula) (e:env) (p:proof) : option (axioms p e |-- subst_simul g e).
  refine (
    let f := proof_goal p in
  match formula_comp g e f e with
    | None => None
    | Some fg_eq =>
      match p with
        | Signed_r (Signed_f pr f1) => 
            if formula_comp f e (Signed_f pr f1) e then Some _ else None
        | Confirms_r (Confirms_f pr f1) => 
            if formula_comp f e (Confirms_f pr f1) e then Some _ else None
        | Tauto_r (Says_f pr f1) p1 => 
            if formula_comp f e (Says_f pr f1) e then if check f1 e p1 then Some _ else None else None
        | Impl_r f3 p1 p2 p3 => 
            if formula_comp f e f3 e
              then match proof_goal p2 with
                     | Impl_f f1 f2 => if check f1 e p1
                                         then if check (Impl_f f1 f2) e p2
                                                then if check (Impl_f f2 f3) e p3 then Some _ else None
                                                else None
                                         else None
                     | _ => None
                   end
              else None
        | Says_Confirms_r (Says_f pr f2) p1 p2 =>
            if formula_comp f e (Says_f pr f2) e
              then match proof_goal p1 with
                     | Confirms_f pr0 f1 => if principal_dec (prsubst pr e) (prsubst pr0 e)
                                              then if check (Confirms_f pr f1) e p1
                                                     then if check (Impl_f f1 f) e p2 then Some _ else None
                                                     else None
                                              else None
                     | _ => None
                   end
              else None
        | Says_Signed_r (Says_f pr f2) p1 p2 =>
            if formula_comp f e (Says_f pr f2) e
              then match proof_goal p1 with
                     | Signed_f pr0 f1 => if principal_dec (prsubst pr e) (prsubst pr0 e)
                                              then if check (Signed_f pr f1) e p1
                                                    then if check (Impl_f f1 f) e p2 then Some _ else None
                                                    else None
                                              else None
                     | _ => None
                   end
              else None
        | Says_Says_r (Says_f pr f2) p1 p2 =>
            if formula_comp f e (Says_f pr f2) e
              then match proof_goal p1 with
                     | Says_f pr0 f1 => if principal_dec (prsubst pr e) (prsubst pr0 e)
                                              then if check (Says_f pr f1) e p1
                                                     then if check (Impl_f f1 f) e p2 then Some _ else None
                                                     else None
                                              else None
                     | _ => None
                   end
              else None
        | Says_Spec_r (Says_f pr f2) theP p1 p2 =>
             if formula_comp f e (Says_f pr f2) e
               then match proof_goal p1 with
                      | Abs_f f1 => if check (Abs_f f1) e p1
                                      then match proof_goal p2 with
                                             | Impl_f pf1 pf2 => if check (Impl_f pf1 pf2) e p2
                                                                   then if formula_comp f e pf2 e
                                                                          then if formula_comp f1 ((Some theP)::e) pf1 e
                                                                                 then Some _
                                                                                 else None
                                                                          else None
                                                                    else None 
                                             | _ => None
                                           end
                                      else None
                      | _ => None
                    end
               else None
        | _ => None
      end
  end) ;
  (* Rewrite equalities *)
    rewrite fg_eq in * ; rewrite _H in * ; subst ; simpl in * ; 
  (* Signed, Confirms, Tauto *)
    try (prove_auth ; auto ; fail).
  (* Impl *)
    eapply (Weaken_e _ (axioms p1 e ++ axioms p2 e ++ axioms p3 e)) in _H0.
    eapply (Weaken_e _ (axioms p1 e ++ axioms p2 e ++ axioms p3 e)) in _H1.
    eapply (Weaken_e _ (axioms p1 e ++ axioms p2 e ++ axioms p3 e)) in _H2.
    eapply (cut_elimination _ (Impl_f (subst_simul f2 e) (subst_simul f3 e))) ; auto.
    eapply Impl_e.
    eapply (cut_elimination _ (Impl_f (subst_simul f1 e) (subst_simul f2 e))) ; auto.
    eapply Impl_e.
    eapply (cut_elimination _ (subst_simul f1 e)) ; auto.
    eapply Init_e. eapply Init_e. eapply Init_e.
    repeat (incl_apps).
    repeat (incl_apps).
    repeat (incl_apps).
  (* Says_Confirms *)
    eapply (Weaken_e _ (axioms p1 e ++ axioms p2 e)) in _H1.
    eapply (cut_elimination _ (Confirms_f (prsubst pr e) (subst_simul f1 e))) ; auto.
    eapply Confirms_e.
    eapply (cut_elimination _ (Impl_f (subst_simul f1 e) (subst_simul f e))) ; auto.
    eapply (Weaken_e _ (subst_simul f1 e :: axioms p1 e ++ axioms p2 e)) in _H2 ; auto ; repeat (incl_apps).
    eapply Impl_e. eapply Init_e.
    rewrite _H. eapply Init_e.
    repeat (incl_apps).
    repeat (incl_apps).
  (* Says_Signed *)
    eapply (Weaken_e _ (axioms p1 e ++ axioms p2 e)) in _H1.
    eapply (cut_elimination _ (Signed_f (prsubst pr e) (subst_simul f1 e))) ; auto.
    eapply Signed_e.
    eapply (cut_elimination _ (Impl_f (subst_simul f1 e) (subst_simul f e))) ; auto.
    eapply (Weaken_e _ (subst_simul f1 e :: axioms p1 e ++ axioms p2 e)) in _H2 ; auto ; repeat (incl_apps).
    eapply Impl_e. eapply Init_e.
    rewrite _H. eapply Init_e.
    repeat (incl_apps).
    repeat (incl_apps).
  (* Says_Says *)
    eapply (Weaken_e _ (axioms p1 e ++ axioms p2 e)) in _H1.
    eapply (cut_elimination _ (Says_f (prsubst pr e) (subst_simul f1 e))) ; auto.
    eapply Says_e.
    eapply (cut_elimination _ (Impl_f (subst_simul f1 e) (subst_simul f e))) ; auto.
    eapply (Weaken_e _ (subst_simul f1 e :: axioms p1 e ++ axioms p2 e)) in _H2 ; auto ; repeat (incl_apps).
    eapply Impl_e. eapply Init_e.
    rewrite _H. eapply Init_e.
    repeat (incl_apps).
    repeat (incl_apps).
  (* Says_Spec *)
    eapply (Weaken_e _ (axioms p1 e ++ axioms p2 e)) in _H0.
    eapply (cut_elimination _ (Abs_f (subst_simul f1 (None :: e)))) ; auto.
    eapply (Spec_e _ theP).
    rewrite subst_subst_simul.
    eapply (Weaken_e _ (subst_simul f1 (Some theP :: e) :: axioms p1 e ++ axioms p2 e)) in _H1.
    eapply (cut_elimination _ (Impl_f (subst_simul pf1 e) (subst_simul pf2 e))) ; auto.
    eapply Impl_e. rewrite _H3. eapply Init_e.
    rewrite _H2. eapply Init_e.
    repeat (incl_apps).
    repeat (incl_apps).
Defined.


(** Testing *)

Definition delegate a b p := Signed_f (Pcpl_p a) (Abs_f (Impl_f (Says_f (Pcpl_p b) (Pred_f p (Var_p 0))) (Pred_f p (Var_p 0)))).

Open Scope string_scope.

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
