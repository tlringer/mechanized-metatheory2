From mm Require Import util stlc.
Set Implicit Arguments.

Module terminating.
  Definition t (P : expr.t -> expr.t -> Prop) (e1 e2 : expr.t) :=
    exists v1 v2,
      step.star e1 v1 /\
      step.star e2 v2 /\
      value.t v1 /\
      value.t v2 /\
      P v1 v2
  .
End terminating.

Fixpoint V ty e1 e2 :=
  match ty with
    | type.unit => e1 = expr.tt /\ e2 = expr.tt
    | type.arrow ty1 ty2 =>
      expr.wf 0 e1 /\
      expr.wf 0 e2 /\
      exists body1 body2,
          e1 = expr.abs body1 /\
          e2 = expr.abs body2 /\
          forall v1 v2,
            V ty1 v1 v2 ->
            terminating.t (V ty2) (expr.subst [v1] body1) (expr.subst [v2] body2)
  end.
Notation E ty :=
  (terminating.t (V ty)).

Lemma V_value :
  forall ty v1 v2,
    V ty v1 v2 ->
    value.t v1 /\ value.t v2.
Proof.
  intros ty v1 v2 HV.
  destruct ty; cbn [V] in HV.
  - intuition; subst; constructor.
  - destruct HV as [WF1 [WF2 [body1 [body2 [? [? _]]]]]].
    intuition; subst; constructor.
Qed.

Lemma V_E :
  forall ty v1 v2,
    V ty v1 v2 ->
    E ty v1 v2.
Proof.
  intros.
  exists v1, v2.
  intuition.
  - firstorder using V_value.
  - firstorder using V_value.
Qed.

Lemma V_closed :
  forall ty v1 v2 ,
    V ty v1 v2 ->
    expr.wf 0 v1 /\ expr.wf 0 v2.
Proof.
  induction ty; simpl; intuition; subst; simpl; auto.
Qed.

Lemma V_list_closed :
  forall G vs1 vs2,
    Forall3 V G vs1 vs2 ->
    Forall (expr.wf 0) vs1 /\ Forall (expr.wf 0) vs2.
Proof.
  intros G vs1 vs2 F.
  split; apply Forall_from_nth.
  - intros n e1 NEe1.
    destruct (Forall3_nth_error2 _ F NEe1) as [ty [e2 [NEty [NEe2 Ve2]]]].
    firstorder using V_closed.
  - intros n e2 NEe2.
    destruct (Forall3_nth_error3 _ F NEe2) as [ty [e1 [NEty [NEe1 Ve1]]]].
    firstorder using V_closed.
Qed.

Lemma E_step1 :
  forall ty e1 e1' e2,
    step.t e1 e1' ->
    E ty e1' e2 ->
    E ty e1 e2.
Proof.
  intros ty e1 e1' e2 S HE.
  revert ty e2 HE.
  induction S; intros ty0 e0 [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]]; exists v1, v2; intuition.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_step2 :
  forall ty e1 e2 e2',
    step.t e2 e2' ->
    E ty e1 e2' ->
    E ty e1 e2.
Proof.
  intros ty e1 e2 e2' S HE.
  revert ty e1 HE.
  induction S; intros ty0 e0 [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]]; exists v1, v2; intuition.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_star1 :
  forall ty e1 e1' e2,
    step.star e1 e1' ->
    E ty e1' e2 ->
    E ty e1 e2.
Proof.
  intros ty e1 e1' e2 Star E12.
  revert ty e2 E12.
  now induction Star; eauto using E_step1.
Qed.

Lemma E_star2 :
  forall ty e1 e2 e2',
    step.star e2 e2' ->
    E ty e1 e2' ->
    E ty e1 e2.
Proof.
  intros ty e1 e2 e2' Star E12.
  revert ty e1 E12.
  now induction Star; eauto using E_step2.
Qed.

Lemma E_star :
  forall ty e1 e1' e2 e2',
    step.star e1 e1' ->
    step.star e2 e2' ->
    E ty e1' e2' ->
    E ty e1 e2.
Proof.
  intros ty e1 e1' e2 e2' Star1 Star2 E12.
  eapply E_star1; [|eapply E_star2]; eauto.
Qed.

Theorem fundamental :
  forall G e ty,
    has_type.t G e ty ->
    forall vs1 vs2,
      Forall3 V G vs1 vs2 ->
      E ty (expr.subst vs1 e) (expr.subst vs2 e).
Proof.
  induction 1; intros vs1 vs2 F.
  - apply V_E.
    destruct (Forall3_nth_error1 _ F H) as [v1 [v2 [NE1 [NE2 V12]]]].
    simpl.
    now rewrite NE1, NE2.
  - apply V_E.
    simpl.
    intuition.
  - apply V_E.
    cbn [V].
    assert (expr.wf (S (length G)) e) as WFe
        by (now apply has_type.wf in H; simpl in * ).
    pose proof F as F0.
    apply Forall3_length in F0.
    destruct F0 as [EGvs1 EGvs2].
    split; [|split].
    + apply expr.wf_subst; firstorder using V_list_closed.
      simpl. now rewrite EGvs1 in *.
    + apply expr.wf_subst; firstorder using V_list_closed.
      simpl. now rewrite EGvs2 in *.
    + exists (expr.subst (expr.descend 1 vs1) e), (expr.subst (expr.descend 1 vs2) e).
      split; [now rewrite expr.descend_1|].
      split; [now rewrite expr.descend_1|].
      intros v1 v2 V12.
      rewrite !expr.subst_cons;
        firstorder using V_list_closed.
      now rewrite EGvs2 in *.
      now rewrite EGvs1 in *.
  - cbn [expr.subst].
    specialize (IHt1 vs1 vs2 F).
    specialize (IHt2 vs1 vs2 F).
    destruct IHt1 as [v11 [v12 [Star11 [Star12 [Val11 [Val12 V1]]]]]].
    destruct IHt2 as [v21 [v22 [Star21 [Star22 [Val21 [Val22 V2]]]]]].
    destruct V1 as [WF1 [WF2 [body1 [body2 [? [? H1]]]]]].
    subst v11 v12.
    eapply E_star; [| |now eauto].

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    eapply step.star_app2. now eauto.
    eauto using step.step_l, step.beta.

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    eapply step.star_app2. now eauto.
    eauto using step.step_l, step.beta.
Qed.
Print Assumptions fundamental.

Corollary fundamental_closed :
  forall e ty,
    has_type.t [] e ty ->
    E ty e e.
Proof.
  intros e ty HT.
  apply fundamental with (vs1 := []) (vs2 := []) in HT; auto.
  now rewrite !expr.subst_identity with (n := 0) in *.
Qed.

Lemma fundamental_value :
  forall v ty,
    has_type.t [] v ty ->
    value.t v ->
    V ty v v.
Proof.
  intros v ty HT Val.
  pose proof fundamental_closed HT as Ev.
  destruct Ev as [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]].
  apply step.star_value in Star1; auto.
  apply step.star_value in Star2; auto.
  subst.
  auto.
Qed.

Corollary termination :
  forall e ty,
    has_type.t [] e ty ->
    exists v, value.t v /\ step.star e v.
Proof.
  intros e ty HT.
  destruct (fundamental_closed HT) as [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]].
  eauto.
Qed.



