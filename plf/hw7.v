Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.


From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Types.
From PLF Require Import Imp.

Hint Constructors multi.

Module S.

Import Smallstep.

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Fixpoint s_compile (e : aexp) : list sinstr :=
match e with
		| ANum v => [SPush v]
		| AId i => [SLoad i]
		| APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
		| AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
		| AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
end.

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic.
  intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

Definition compiler_is_correct_statement : Prop :=
  forall (st : state) (e : aexp),
    stack_multistep st (s_compile e, []) ([], [ aeval st e ]).


Theorem s_compile_aux : forall (e : aexp) (t: prog) (st : state) (stk1 : stack),
  stack_multistep st (s_compile e ++ t, stk1) (t, aeval st e :: stk1).
Proof.

induction e.
  - intros t st stk1. simpl. unfold stack_multistep. apply multi_R. constructor.
  - intros t st stk1. simpl. unfold stack_multistep. apply multi_R. constructor.
  - intros t st stk1. simpl. unfold stack_multistep. 
    unfold stack_multistep in IHe1. unfold stack_multistep in IHe2.
    eapply multi_trans.
    + rewrite <- app_assoc. rewrite <- app_assoc. eapply IHe1.
    + eapply multi_trans.
      * eapply IHe2.
      * apply multi_R. constructor.
  - (* same as previous case *)
    intros t st stk1. simpl. unfold stack_multistep. 
    unfold stack_multistep in IHe1. unfold stack_multistep in IHe2.
    eapply multi_trans.
    + rewrite <- app_assoc. rewrite <- app_assoc. eapply IHe1.
    + eapply multi_trans.
      * eapply IHe2.
      * apply multi_R. constructor.
  - (* same as previous case *)
    intros t st stk1. simpl. unfold stack_multistep. 
    unfold stack_multistep in IHe1. unfold stack_multistep in IHe2.
    eapply multi_trans.
    + rewrite <- app_assoc. rewrite <- app_assoc. eapply IHe1.
    + eapply multi_trans.
      * eapply IHe2.
      * apply multi_R. constructor.
Qed.


Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
  unfold compiler_is_correct_statement.
  intros st e.
  rewrite <- (app_nil_r (s_compile e)).
  apply s_compile_aux.
Qed.


End S.

Module T.

Import Types.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

Proof with auto.
  intros t T HT.
  induction HT...
  (* The cases that were obviously values, like T_Tru and
     T_Fls, were eliminated immediately by auto *)
  - (* T_Test *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 can take a step *)
      inversion H as [t1' H1].
      exists (test t1' t2 t3)...

  - (* T_Succ *)
    inversion IHHT.
    + left. apply (nat_canonical t1 HT) in H.
      apply nv_scc in H. unfold value. right. assumption.
    + right. inversion H as [t1' H1]. exists (scc t1')...
  - (* T_Prd *)
    right. inversion IHHT; clear IHHT.
    + apply (nat_canonical t1 HT) in H.
      inversion H; subst; clear H.
      * exists zro...
      * exists t...
    + inversion H. exists (prd x). apply ST_Prd. assumption.
  - (* T_Iszro *)
    right. inversion IHHT; clear IHHT.
    + apply (nat_canonical t1 HT) in H.
      inversion H; subst; clear H.
      * exists tru. apply ST_IszroZro.
      * exists fls. apply ST_IszroScc.  assumption.
    + inversion H. exists (iszro x). apply ST_Iszro. assumption.
Qed.


Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    - (* T_Scc *) inversion HE; subst; clear HE.
      apply T_Scc. apply IHHT. assumption.
    - (* T_Prd *) inversion HE; subst; clear HE.
      + apply HT.
      + inversion HT. assumption.
      + apply T_Prd. apply IHHT. assumption.
    - (* T_Iszro *) inversion HE; subst; clear HE.
      + apply T_Tru.
      + apply T_Fls.
      + apply T_Iszro. apply IHHT. assumption.
Qed. 

  
End T.