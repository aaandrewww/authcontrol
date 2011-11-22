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
    | Pred_f s v => Pred_f s (subst_p v n a)
    | Impl_f f1 f2 => Impl_f (subst f1 n a) (subst f2 n a)
    | Says_f v f => Says_f (subst_p v n a) (subst f n a)
    | Confirms_f v f => Confirms_f (subst_p v n a) (subst f n a)
    | Signed_f v f => Signed_f (subst_p v n a) (subst f n a)
    | Abs_f f => Abs_f (subst f (n+1) a)
  end.

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
                                 (Says_f a (Abs_f f1))::C |-- Says_f a f2
| Weaken_e : forall C1 C2 f, C1 |-- f -> incl C1 C2 -> C2 |-- f (* should prove as a lemma? *)
where "C '|--' F" := (entails C F).

(** The main lemma about the logic *)
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
 | Assump_r : formula -> proof (* formula is an assumption *)
 | Tauto_r : formula -> proof -> proof (* formula = Says_f a f, proof of f *) 
 | Weaken_Impl_r : formula -> proof -> proof (* formula = Impl_f f1 f2, proof of f2 (with f1 in context) *)
 | Impl_r : formula -> proof -> proof -> proof (* formula = f2, proof of f1, Impl_f f1 f2 *)
 | Says_Confirms_r : formula -> proof -> proof -> proof (* formula = Says_f a f2, proof of Confirms_f a f1, Says_f a f2 given f1*) 
 | Says_Signed_r : formula -> proof -> proof -> proof (* formula = Says_f a f2, proof of Signed_f a f1, Says_f a f2 given f1*) 
 | Says_Says_r : formula -> proof -> proof -> proof (* formula = Says_f a f2, proof of Says_f a f1, Says_f a f2 given f1*) 
 | Says_Spec_r : formula -> pcpl -> proof -> proof -> proof. (* formula = Says_f a f2, principal = p, proof of Says_f a Abs_f f1, Says_f a f2 given subst f1 0 p *)

Definition proof_goal p : formula :=
match p with
  | Signed_r f => f
  | Confirms_r f => f
  | Tauto_r f _ => f
  | Weaken_Impl_r f _ => f
  | Impl_r f _ _ => f
  | Says_Confirms_r f _ _ => f 
  | Says_Signed_r f _ _ => f
  | Says_Says_r f _ _ => f
  | Says_Spec_r f _ _ _ => f
  | Assump_r f => f
end.

Fixpoint axioms (p:proof) : context :=
match p with
  | Signed_r f => f::nil
  | Confirms_r f => f::nil
  | Tauto_r f p1 => axioms p1
  | Weaken_Impl_r f p1 => axioms p1
  | Impl_r f p1 p2 => List.app (axioms p1) (axioms p2)
  | Says_Confirms_r f p1 p2 => List.app (axioms p1) (axioms p2) 
  | Says_Signed_r f p1 p2 => List.app (axioms p1) (axioms p2)
  | Says_Says_r f p1 p2 => List.app (axioms p1) (axioms p2)
  | Says_Spec_r f a p1 p2 => List.app (axioms p1) (axioms p2)
  | Assump_r _ => nil
end.

Fixpoint assumps (p:proof) : context :=
match p with
  | Signed_r f => nil
  | Confirms_r f => nil
  | Tauto_r f p1 => assumps p1
  | Weaken_Impl_r f p1 => assumps p1
  | Impl_r f p1 p2 => List.app (assumps p1) (assumps p2)
  | Says_Confirms_r f p1 p2 => List.app (assumps p1) (assumps p2)
  | Says_Signed_r f p1 p2 => List.app (assumps p1) (assumps p2)
  | Says_Says_r f p1 p2 => List.app (assumps p1) (assumps p2)
  | Says_Spec_r f a p1 p2 => List.app (assumps p1) (assumps p2)
  | Assump_r f => f::nil
end.

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

Lemma incl_app_cons : forall A (l1 l2:list A) (m:A), incl (l1 ++ m :: l2) (m :: l1 ++ l2).
Proof.
  intros.
  apply incl_app.
  repeat incl_apps.
  apply incl_cons.
  apply in_eq.
  repeat incl_apps.
Qed.

Lemma incl_app_app : forall A (l1 l2 l3: list A), incl (l1 ++ l3) ((l1 ++ l2) ++ l3).
Proof.
  intros.
  apply incl_app.
  repeat incl_apps.
  apply incl_appl.
  repeat incl_apps.
  repeat incl_apps.
Qed.  

Lemma incl_app_app2 : forall A (l1 l2 l3: list A), incl (l1 ++ l3) ((l2 ++ l1) ++ l3).
Proof.
  intros.
  apply incl_app.
  apply incl_appl.
  repeat incl_apps.
  repeat incl_apps.
Qed.

Lemma incl_app_cons2 : forall A (l1 l2 l3:list A) (m:A), incl (l1 ++ m :: l2) (m :: (l3 ++ l1) ++ l2).
Proof.
  intros.
  apply incl_app.
  apply incl_tl.
  apply incl_appl.
  repeat incl_apps.
  apply incl_cons.
  apply in_eq.
  repeat incl_apps.
Qed.

Lemma incl_app_cons3 : forall A (l1 l2 l3: list A) m, incl (l1 ++ m :: l2) 
  ((m :: l3 ++ l1) ++ l2).
Proof.
  intros.
  apply incl_app.
  apply incl_appl.
  repeat incl_apps.
  apply incl_cons.
  apply in_eq.
  repeat incl_apps.
Qed.

Fixpoint member (f:formula) (C:context) : option (In f C).
refine (
  match C with 
    | nil => None
    | p::rest => if formula_dec f p then Some _ else None
  end).
  unfold In. left. auto.
Defined.
 
(** Proof checker - Checks the proof tree from the bottom up. *)
Fixpoint check (g:formula) (p:proof) (c:context) : option (axioms p ++ c |-- g).
  refine (
    let f := proof_goal p in
  if formula_dec g f then
      match p with
        | Signed_r (Signed_f pr f1) => 
            if formula_dec f (Signed_f pr f1) then Some _ else None
        | Confirms_r (Confirms_f pr f1) => 
            if formula_dec f (Confirms_f pr f1) then Some _ else None
        | Tauto_r (Says_f pr f1) p1 => 
            if formula_dec f (Says_f pr f1) then if check f1 p1 c then Some _ else None else None
        | Weaken_Impl_r (Impl_f f1 f2) p1 =>
            if formula_dec f (Impl_f f1 f2) then if check f2 p1 (f1::c) then Some _ else None else None
        | Impl_r f2 p1 p2 => 
            if formula_dec f f2
              then let pf1 := proof_goal p1
                    in if check pf1 p1 c
                         then match proof_goal p2 with
                                | Impl_f pf2 pf => if formula_dec pf1 pf2
                                                     then if formula_dec pf f
                                                           then if check (Impl_f pf2 pf) p2 c then Some _ else None
                                                           else None
                                                     else None
                                | _ => None
                              end
                         else None
              else None
        | Says_Confirms_r (Says_f pr f2) p1 p2 =>
            if formula_dec f (Says_f pr f2)
              then match proof_goal p1 with
                     | Confirms_f pr0 f1 => if principal_dec pr pr0
                                              then if check (Confirms_f pr f1) p1 c
                                                     then if check f p2 (f1::c) then Some _ else None
                                                     else None
                                              else None
                     | _ => None
                   end
              else None
        | Says_Signed_r (Says_f pr f2) p1 p2 =>
            if formula_dec f (Says_f pr f2)
              then match proof_goal p1 with
                     | Signed_f pr0 f1 => if principal_dec pr pr0
                                              then if check (Signed_f pr f1) p1 c
                                                     then if check f p2 (f1::c) then Some _ else None
                                                     else None
                                              else None
                     | _ => None
                   end
              else None
        | Says_Says_r (Says_f pr f2) p1 p2 =>
            if formula_dec f (Says_f pr f2)
              then match proof_goal p1 with
                     | Says_f pr0 f1 => if principal_dec pr pr0
                                              then if check (Says_f pr f1) p1 c
                                                     then if check f p2 (f1::c) then Some _ else None
                                                     else None
                                              else None
                     | _ => None
                   end
              else None
        | Says_Spec_r (Says_f pr f2) theP p1 p2 =>
             if formula_dec f (Says_f pr f2)
               then match proof_goal p1 with
                      | Says_f pr0 (Abs_f f1) => if principal_dec pr pr0
                                                then if check (Says_f pr0 (Abs_f f1)) p1 c
                                                  then if check f p2 ((subst f1 0 theP)::c) then Some _ else None
                                                  else None
                                                else None
                      | _ => None
                    end
               else None
        | Assump_r f => if formula_dec f g then if member f c then Some _ else None else None
        | _ => None
      end
  else None) ;
  (* Rewrite equalities *)
    try (rewrite _H in * ; rewrite _H0 in * ; subst ; simpl in *) ;
  (* Signed, Confirms, Tauto *)
    try (prove_auth ; auto ; fail).
  (* Assump *)
    assert (f :: c |-- f).
    eapply Init_e.
    eapply (Weaken_e _ c) in H ; auto.
    apply incl_cons ; auto ; apply incl_refl.
  (* Weaken_Impl *)
    eapply Weaken_Impl_e.
    eapply (Weaken_e _ (f1 :: axioms p1 ++ c)) in _H1 ; auto.
    apply incl_app_cons.
  (* Impl *)
    rewrite _H2 in *.
    eapply (Weaken_e _ ((axioms p1 ++ axioms p2) ++ c)) in _H4 ; auto.
    eapply (cut_elimination _ (Impl_f pf2 f2)) ; auto.
    eapply Impl_e.
    eapply (Weaken_e _ ((axioms p1 ++ axioms p2) ++ c)) in _H1 ; auto.
    apply incl_app_app.
    eapply Init_e.
    apply incl_app_app2.
   (* Says_Confirms *)
    eapply (Weaken_e _ ((axioms p1 ++ axioms p2) ++ c)) in _H2.
    eapply (cut_elimination _ (Confirms_f pr0 f1)) ; auto.
    eapply Confirms_e.
    eapply (Weaken_e _ (f1 :: (axioms p1 ++ axioms p2) ++ c)) in _H3 ; auto.
    apply incl_app_cons2.
    apply incl_app_app.
  (* Says_Signed *)
    eapply (Weaken_e _ ((axioms p1 ++ axioms p2) ++ c)) in _H2.
    eapply (cut_elimination _ (Signed_f pr0 f1)) ; auto.
    eapply Signed_e.
    eapply (Weaken_e _ (f1 :: (axioms p1 ++ axioms p2) ++ c)) in _H3 ; auto.
    apply incl_app_cons2.
    apply incl_app_app.
  (* Says_Says *)
    eapply (Weaken_e _ ((axioms p1 ++ axioms p2) ++ c)) in _H2.
    eapply (cut_elimination _ (Says_f pr0 f1)) ; auto.
    eapply Says_e.
    eapply (Weaken_e _ (f1 :: (axioms p1 ++ axioms p2) ++ c)) in _H3 ; auto.
    apply incl_app_cons2.
    apply incl_app_app.
  (* Says_Spec *)
    eapply (Weaken_e _ ((axioms p1 ++ axioms p2) ++ c)) in _H2.
    eapply (cut_elimination _ (Says_f pr0 (Abs_f f3))) ; auto.
    eapply (Spec_e _ theP).
    (*| Weaken_e : forall C1 C2 f, C1 |-- f -> incl C1 C2 -> C2 |-- f *)
    eapply (Weaken_e _ (subst f3 0 theP :: (axioms p1 ++ axioms p2) ++ c)) in _H3 ; auto.
    apply incl_app_cons3.
    apply incl_app_app.
Defined.

Definition check_bool g p c :=
  match check g p c with
    | Some _ => true
    | None => false
  end.

(** Testing *)

Definition delegate b p := Abs_f (Impl_f (Says_f (Pcpl_p b) (Pred_f p (Var_p 0))) (Pred_f p (Var_p 0))).
Definition approve c p := (Pred_f p (Pcpl_p c)).

Definition delegate_signed a b p := Signed_f (Pcpl_p a) (delegate b p).

Open Scope string_scope.

Definition signed sayer f := Signed_r (Signed_f sayer f).

Eval compute in check (Signed_f (Pcpl_p "A") (Pred_f "ok" (Pcpl_p "B"))) (signed (Pcpl_p "A") (Pred_f "ok" (Pcpl_p "B"))) nil.

Definition says_from_assump sayer f := Tauto_r (Says_f (Pcpl_p sayer) f) (Assump_r f).
Definition says_from_signed sayer f := Says_Signed_r (Says_f (Pcpl_p sayer) f) (signed (Pcpl_p sayer) f) (says_from_assump sayer f).

Eval compute in check (Says_f (Pcpl_p "A") (Pred_f "ok" (Pcpl_p "B"))) (says_from_signed "A" (Pred_f "ok" (Pcpl_p "B"))) nil.

Definition delegate_from_signed a b p := Signed_r (delegate_signed a b p). 

Definition valid proof := check_bool (proof_goal proof) proof (assumps proof).

Eval compute in let p := "ok" in
              let a := "A" in
              let b := "B" in
              let c := "C" in
              let bapprove := says_from_signed b (approve c p) in
              let assumed := Assump_r (Impl_f (Says_f (Pcpl_p b) (Pred_f p (Pcpl_p c))) (Pred_f p (Pcpl_p c))) in
              let proof := (Impl_r (Pred_f p (Pcpl_p c)) bapprove  assumed) in
                check (proof_goal proof) proof (assumps assumed).

Definition approval_proof b c p := says_from_signed b (approve c p).
Definition delegation_proof a b p := says_from_signed a (delegate b p).

Definition use_delegation (a b c:pcpl) (p:string) (dp ap:proof) :=
  Says_Spec_r (Says_f (Pcpl_p a) (approve c p)) c dp (Tauto_r (Says_f (Pcpl_p a) (approve c p))
    (Impl_r (approve c p) ap (Assump_r (Impl_f (Says_f (Pcpl_p b) (Pred_f p (Pcpl_p c))) (Pred_f p (Pcpl_p c)))))).

Eval compute in let p := "ok" in
              let a := "A" in
              let b := "B" in
              let c := "C" in
              let dp := delegation_proof a b p in
              let ap := approval_proof b c p in
              let ud := use_delegation a b c p dp ap in
                check (proof_goal ud) ud nil.