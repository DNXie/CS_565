(*-------------------------------------------------
*   CS 565, Spring 2020 Final Exam
*                                                 
*   Total: 160 points
*   Due: 9AM, May 6, 2020
*                                                 
*   You are free to use any material from the text, including any
*   introduced tactics, and proven lemmas and theorems.  You can additionally 
*   use any tactics available in the Coq Standard Library (including auto,
*   tauto, etc.)  You are also free prove additional lemmas if that
*   would help facilitate completing your proofs.  You cannot, however
*   change the set of required libraries given in the beginnning of this 
*   file.
*                                                 
*   There will be no partial credit given for incomplete proofs.
*                                                 
*----------------------------------------------------*)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

Import ListNotations.

From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Imp.
From PLF Require Hoare.
From PLF Require Hoare2.
From PLF Require Stlc.
From PLF Require StlcProp.
From PLF Require References.
From PLF Require Sub.

Module Prop_Ex.

(* Question 1: 20 points *)
  
Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
   (st =[ c1 ]=> st') -> (st =[c2]=> st').

Theorem F: forall c1 c2: com, exists Z: com -> Prop, (Z c1) -> capprox c1 c2 -> (Z c2).
Proof.
  intros. exists (fun c => True). intros. assumption.
Qed.

(* Question 2: 10 points *)

Inductive H : nat -> Prop :=
     h_0 : H 0
   | h_plus3 : forall n, H n -> H (3+n)
   | h_plus5 : forall n, H n -> H (5+n).

Definition HDef (n : nat) (A : (H n)) :  H (5 + (8 + n)).
Proof.
  apply h_plus5. apply h_plus5. apply h_plus3. assumption.
Qed.

End Prop_Ex.  

Module Hoare_Ex.

Import Hoare.
Import Hoare2.

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(* Question 3:  15 points *)

Theorem is_wp_example : 
  is_wp (fun st => st Y <= 4)
    (X ::= Y + 1) (fun st => st X <= 5).
Proof.
  unfold is_wp. split. 
  - eapply hoare_consequence_pre.
    apply hoare_asgn. intros st H. unfold assn_sub.
    unfold t_update. simpl. omega. 
  - intros. unfold hoare_triple in H.
    unfold assert_implies. intros.
    assert (H1: t_update st X ((st Y) + 1 ) X <= 5).
    { eapply H. constructor. unfold aeval. reflexivity.
      assumption. }
    unfold t_update in H1. simpl in H1. omega.
Qed.

(* Question 4: 10 points *)

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

Lemma wp_invariant : forall b c Inv Q,
    Inv = wp (WHILE b DO c END) Q
    -> {{ fun st => Inv st /\ bassn b st }} c {{ Inv }}.
Proof.
  intros. unfold wp in H. subst. unfold hoare_triple. intros.
  destruct H0 as [H2 H3]. apply H2. 
  rename s' into st''. 
  destruct (beval st b) eqn:E.
  - apply E_WhileTrue with (st':=st'); assumption.
  - apply bexp_eval_false in H3. 
    * exfalso. assumption.
    * assumption.
Qed.

End Hoare_Ex.

Module Stlc_Ex.

Import Stlc.
Import StlcProp.
Import Stlc.STLC.
Import StlcProp.STLCProp.

(* Question 5 (10 points) *)
(* Reframe the subst definition given above as an inductive relation *)

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2 : forall x',
      x <> x' ->
      substi s x (var x') (var x')
  | s_abs1 : forall T t,
      substi s x (abs x T t) (abs x T t)
  | s_abs2: forall y T t t',
      x <> y ->
      substi s x t t' ->
      substi s x (abs y T t) (abs y T t')
  | s_app : forall t1 t1' t2 t2', 
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (app t1 t2) (app t1' t2')
  | s_tru : substi s x tru tru
  | s_fls : substi s x fls fls
  | s_test : forall t1 t1' t2 t2' t3 t3', 
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x (test t1 t2 t3) (test t1' t2' t3').

(* Question 6 (20 points) *)

Hint Constructors value.
Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  intros s x0 t t'. split.
  - generalize dependent t'. induction t; subst.
    + intros. unfold subst in H.
      destruct (eqb_string x0 s0) eqn:H1.
      * apply eqb_string_true_iff in H1. subst. apply s_var1.
      * apply eqb_string_false_iff in H1. subst. apply s_var2. assumption.
    + intros. assert (Heq: [x0:=s](app t1 t2) = app ([x0:=s]t1) ([x0:=s]t2)).
      { reflexivity. }
      rewrite Heq in H. rewrite <- H. apply s_app.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + intros. simpl in H.
      destruct (eqb_string x0 s0) eqn:H1.
      * apply eqb_string_true_iff in H1. subst. constructor.
      * apply eqb_string_false_iff in H1. subst. eapply s_abs2.
        assumption. apply IHt. reflexivity.
    + intros. unfold subst in H. subst. constructor.
    + intros. unfold subst in H. subst. constructor.
    + intros. assert (Heq: [x0:=s](test t1 t2 t3) = test ([x0:=s]t1) ([x0:=s]t2) ([x0:=s]t3)).
      { reflexivity. }
      rewrite Heq in H. rewrite <- H. clear Heq. apply s_test.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
      * apply IHt3. reflexivity.
  - generalize dependent t'. induction t; subst; intros.
    + unfold subst. inversion H; subst.
      * rewrite <- eqb_string_refl. reflexivity.
      * apply eqb_string_false_iff in H1. rewrite H1. reflexivity.
    + inversion H; subst. apply IHt1 in H2. apply IHt2 in H4. subst. reflexivity.
    + simpl. destruct (eqb_string x0 s0) eqn:H1.
      * inversion H; subst. reflexivity. unfold not in H5. 
        apply eqb_string_true_iff in H1. apply H5 in H1. inversion H1.
      * inversion H; subst. 
        ** apply eqb_string_false_iff in H1. unfold not in H1.
            exfalso. apply H1. reflexivity. 
        ** apply IHt in H6. subst. reflexivity.
    + inversion H; subst. reflexivity.
    + inversion H; subst. reflexivity.
    + inversion H; subst. apply IHt1 in H3. apply IHt2 in H5. apply IHt3 in H6.
      subst. reflexivity.
Qed.

(* Question 7: 10 points *)

Theorem subject_expansion_false : forall t' T,
    empty |- t' \in T  ->
    exists t, t --> t' -> not (empty |- t \in T).
Proof.
  intros. 
  exists (test tru tru (app tru tru)).
  intros. unfold not. intro. inversion H1. subst. inversion H8. subst. 
  inversion H9. subst. inversion H5. 
Qed.

(* Question 8: 10 points *)

Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
  intros. generalize dependent T'. induction H; intros. 
  + inversion H0. subst. rewrite H in H3. injection H3 as H3. 
    assumption.
  + inversion H0. subst. apply IHhas_type in H6. subst. 
    reflexivity.
  + inversion H1. subst. apply IHhas_type1 in H5.
    injection H5. intros. subst. reflexivity.
  + inversion H0. reflexivity.
  + inversion H0. reflexivity.
  + inversion H2. subst. apply IHhas_type2 in H9.  assumption.
Qed.

(* Question 9: 15 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros. unfold stuck, not. intros. 
  destruct H1 as [H2 H3].
  unfold normal_form in H2.
  induction H0.
  - apply progress in H. destruct H as [H|H].
    * apply H3. assumption.
    * apply H2. assumption.
  - apply IHmulti.
    * apply preservation with (t:=x0); assumption.
    * assumption.
    * assumption.
Qed.

End Stlc_Ex.

Module Refs_Ex.

Import References.STLCRef.
Import References.STLCRef.ExampleVariables.  
Import References.STLCRef.RefsAndNontermination.

(* Question 10 (15 points) *)
(* Write a definition of factorial using references and without using fix *)

(* store factorial_body in reference f. call itself *)
(* \x:Nat. if test0 x then 1 else x * ((!f) (pred x)) *)
Definition f := "f".
Definition factorial_body : tm :=
  (abs x Nat 
    (test0 (var x)
      (const 1)
      (mlt (var x)
        (app (deref (var f)) (prd (var x)))
      )
    )
  ).


(* \s:Nat. 
  apply \f:Ref(Nat->Nat).
    f := factorial_body
    (!f s) 
  in
    ref (\x:Nat. 0)  [dummy]
*)
Definition factorial : tm :=
  (abs s Nat
    (app 
      (abs f (Ref (Arrow Nat Nat))
        (tseq (assign (var f) factorial_body)
              (app (deref (var f)) (var s))
        )
      )
     (ref (abs x Nat (const 0)))
    )
  ).

Lemma factorial_4 : exists st,
  app factorial (const 4) / nil -->* const 24 / st.
Proof.
  eexists. unfold factorial. reduce.  
Qed.
 
(* Question 11 (10 points) *)
Lemma factorial_type : empty; nil |- factorial \in (Arrow Nat Nat).
Proof with eauto.
  unfold factorial. unfold factorial_body.
  eapply T_Abs...
  eapply T_App...
  eapply T_Abs...
  unfold tseq.
  eapply T_App...
  eapply T_Abs...
  eapply T_Assign...
  eapply T_Abs...
  eapply T_If0...
  eapply T_Mult...
  eapply T_App...
Qed.


End Refs_Ex.

Module Sub_Ex.

Import Sub.

(* Question 12: 15 points *)

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: Arrow V1 V2 ->
     exists U1 U2,
     U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; subst; try solve_by_invert.
  - intros. exists V1. exists V2. split. 
    + assumption.
    + split...
  - intros. apply IHHs2 in HeqV. destruct HeqV as [U1 [U2 [H1 [H2 H3]]]].
    apply IHHs1 in H1. destruct H1 as [U3 [U4 [H4 [H5 H6]]]].
    exists U3. exists U4. split...
  - intros. discriminate HeqV.
  - intros. injection HeqV. intros. subst. exists S1, S2.
    split...
Qed.

End Sub_Ex.