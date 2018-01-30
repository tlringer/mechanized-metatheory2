(*
 * Minimizing STLC example
 *)


From mm Require Import util abt.

Print clos_refl_trans_n1.

Module old.

Module exprop.
  Inductive t' :=
  | abs
  | app
  | tt
  | ff
  | If
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tt => []
    | ff => []
    | If => [0; 0; 0]
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End exprop.

Module type.
  Inductive t :=
  | bool
  | arrow : t -> t -> t
  .
End type.

Module expr_abt := abt.abt exprop.

Module expr_ast.
  Inductive t :=
  | var (x : nat) : t
  | abs : t -> t
  | app : t -> t -> t
  | tt : t
  | ff : t
  | If : t -> t -> t -> t
  .
End expr_ast.

Module expr_basis.
  Module A := expr_abt.

  Import expr_ast.
  Definition t := t.

  Fixpoint to_abt (ty : t) : A.t :=
    match ty with
    | var n => A.var n
    | abs e' => A.op exprop.abs [A.bind 1 (to_abt e')]
    | app e1 e2 => A.op exprop.app [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
    | tt => A.op exprop.tt []
    | ff => A.op exprop.ff []
    | If e1 e2 e3 => A.op exprop.If [A.bind 0 (to_abt e1);
                                            A.bind 0 (to_abt e2);
                                            A.bind 0 (to_abt e3)]
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op exprop.abs [A.bind 1 a'] => abs (of_abt a')
    | A.op exprop.app [A.bind 0 a1; A.bind 0 a2] => app (of_abt a1) (of_abt a2)
    | A.op exprop.tt [] => tt
    | A.op exprop.ff [] => ff
    | A.op exprop.If [A.bind 0 a1; A.bind 0 a2; A.bind 0 a3] =>
      If (of_abt a1) (of_abt a2) (of_abt a3)
    | _ => var 0 (* bogus *)
    end.

  Fixpoint shift c d (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else x + d)
    | abs e' => abs (shift (S c) d e')
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (shift c d e1) (shift c d e2) (shift c d e3)
    end.

  Fixpoint subst rho e :=
    match e with
    | var x => match nth_error rho x with
                  | Some e' => e'
                  | None => e
                  end
    | abs e' => abs (subst (var 0 :: map (shift 0 1) rho) e')
    | app e1 e2 => app (subst rho e1) (subst rho e2)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (subst rho e1) (subst rho e2) (subst rho e3)
    end.

  Fixpoint wf n e :=
    match e with
    | var x => x < n
    | abs e' => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
    | tt => True
    | ff => True
    | If e1 e2 e3 => wf n e1 /\ wf n e2 /\ wf n e3
    end.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

  Lemma ws_to_abt : forall e, A.ws (to_abt e).
  Proof. A.basis_util.prove_ws_to_abt. Qed.

  Lemma of_to_abt : forall e, of_abt (to_abt e) = e.
  Proof. A.basis_util.prove_of_to_abt. Qed.

  Lemma to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.
  Proof. A.basis_util.prove_to_of_abt to_abt of_abt. Qed.

  Lemma shift_to_abt_comm : forall e c d, to_abt (shift c d e) = A.shift c d (to_abt e).
  Proof. A.basis_util.prove_shift_to_abt_comm. Qed.

  Lemma map_shift_to_abt_comm :
    forall c d rho, map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).
  Proof. A.basis_util.prove_map_shift_to_abt_comm shift_to_abt_comm. Qed.

  Lemma subst_to_abt_comm : forall e rho,
      to_abt (subst rho e) = A.subst (map to_abt rho) (to_abt e).
  Proof. A.basis_util.prove_subst_to_abt_comm t map_shift_to_abt_comm. Qed.

  Lemma wf_to_abt : forall e n, wf n e <-> A.wf n (to_abt e).
  Proof. A.basis_util.prove_wf_to_abt. Qed.

  Lemma identity_subst_to_abt_comm :
    forall n, List.map to_abt (identity_subst n) = A.identity_subst n.
  Proof. A.basis_util.prove_identity_subst_to_abt_comm map_shift_to_abt_comm. Qed.

  Definition var := var.
  Arguments var /.
  Lemma var_to_abt : forall n, to_abt (var n) = A.var n.
  Proof. reflexivity. Qed.
End expr_basis.

Module expr.
  Include abt.abt_util expr_basis.
  Notation abs := expr_ast.abs.
  Notation app := expr_ast.app.
  Notation tt := expr_ast.tt.
  Notation ff := expr_ast.ff.
  Notation If := expr_ast.If.
End expr.

Module value.
  Inductive t : expr.t -> Prop :=
  | tt : t expr.tt
  | ff : t expr.ff
  | abs : forall e, t (expr.abs e)
  .
End value.

Module step.
  Inductive t : expr.t -> expr.t -> Prop :=
  | beta : forall e1 e2,
      t (expr.app (expr.abs e1) e2)
        (expr.subst [e2] e1)
  | app1  : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.app e1 e2) (expr.app e1' e2)
  | app2  : forall e1 e2 e2',
      t e2 e2' ->
      t (expr.app e1 e2) (expr.app e1 e2')
  | IfT : forall e2 e3,
      t (expr.If expr.tt e2 e3) e2
  | IfF : forall e2 e3,
      t (expr.If expr.ff e2 e3) e3
  | If : forall e1 e1' e2 e3,
      t e1 e1' ->
      t (expr.If e1 e2 e3) (expr.If e1' e2 e3)
  .
  Hint Constructors t.

  (* 
   * Inlining star explicitly as an application of clos_refl_trans_n1 to
   * make it clearer what these proofs are doing for patching purposes
   *)
  Inductive star (e1 : expr.t) : expr.t -> Prop :=
    | star_refl : star e1 e1
    | star_trans (e2 e3 : expr.t) :
        t e2 e3 -> star e1 e2 -> star e1 e3.

  Inductive star_l (e1 : expr.t) : expr.t -> Prop :=
    | star_step_l (e2 : expr.t) : t e1 e2 -> star_l e1 e2
    | star_refl_l : star_l e1 e1
    | star_trans_l (e2 e3 : expr.t) :
        star_l e1 e2 -> star_l e2 e3 -> star_l e1 e3.

  Lemma star_l_star : forall e1 e2,
    star_l e1 e2 -> star e1 e2.
  Proof.
    intros. induction H.
    - apply star_trans with (e2 := e1).
      + auto.
      + constructor.
    - apply star_refl.
    - elim IHstar_l2; auto.
      intros.
      eapply star_trans; eauto.
  Qed.

  Lemma star_star_l : forall e1 e2,
    star e1 e2 -> star_l e1 e2.
  Proof.
    intros. induction H.
    - apply star_refl_l.
    - apply star_trans_l with (e2 := e2).
      + auto.
      + apply star_step_l. auto.
  Qed. 

  Lemma step_l :
    forall e1 e2 e3,
      t e1 e2 ->
      star e2 e3 ->
      star e1 e3.
  Proof.
    intros e1 e2 e3 S Star.
    apply star_l_star.
    apply star_star_l in Star.
    eapply star_trans_l; eauto using star_step_l.
  Qed.

  Lemma star_app1 :
    forall e1 e1' e2,
      star e1 e1' ->
      star (expr.app e1 e2) (expr.app e1' e2).
  Proof.
    intros e1 e1' e2 Star.
    induction Star.
    - constructor.
    - apply star_trans with (e2 := expr.app e0 e2).
      + auto.
      + apply IHStar.
  Qed.

  Lemma star_app2 :
    forall e1 e2 e2',
      star e2 e2' ->
      star (expr.app e1 e2) (expr.app e1 e2').
  Proof.
    intros e1 e2 e2' Star.
    induction Star.
    - constructor.
    - apply star_trans with (e2 := expr_ast.app e1 e0).
      + auto.
      + apply IHStar.
  Qed.

  Lemma star_trans' :
    forall e1 e2 e3,
      star e1 e2 ->
      star e2 e3 ->
      star e1 e3.
  Proof.
    intros e1 e2 e3 S1 S2.
    apply star_star_l in S1.
    apply star_star_l in S2.
    apply star_l_star.
    eauto using star_trans_l.
  Qed.

  Lemma star_refl' :
    forall e,
      star e e.
  Proof.
    constructor.
  Qed.

End step.

Module terminating.
  Definition t (P : expr.t -> Prop) (e : expr.t) :=
    exists v,
      step.star e v /\
      value.t v /\
      P v
  .
End terminating.

Fixpoint V ty e :=
  match ty with
    | type.bool => e = expr.tt \/ e = expr.ff
    | type.arrow ty1 ty2 =>
      expr.wf 0 e /\
      exists body,
          e = expr.abs body /\
          forall e2,
            V ty1 e2 ->
            terminating.t (V ty2) (expr.subst [e2] body)
  end.

Lemma E_step :
  forall ty e e',
    step.t e e' ->
    terminating.t (V ty) e' ->
    terminating.t (V ty) e.
Proof.
  intros ty e e' S HE.
  revert ty HE.
  induction S; intros ty0 [v [Star [Val HV]]]; exists v; intuition.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_star :
  forall ty e e',
    step.star e e' ->
    terminating.t (V ty) e' ->
    terminating.t (V ty) e.
Proof.
  intros ty e e' Star HE.
  revert ty HE.
  now induction Star; eauto using E_step.
Qed.

Module has_sem_type.
  Definition t G e ty :=
    expr.wf (length G) e /\
    forall vs,
      Forall2 V G vs ->
      terminating.t (V ty) (expr.subst vs e).

  Lemma app :
    forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2.
  Proof.
    intros G e1 e2 ty1 ty2.
    intros [WF1 HT1].
    intros [WF2 HT2].
    split; [now cbn; auto|].
    intros vs F.

    cbn [expr.subst].
    specialize (HT1 vs F).
    specialize (HT2 vs F).
    destruct HT1 as [v1 [Star1 [Val1 V1]]].
    destruct HT2 as [v2 [Star2 [Val2 V2]]].
    destruct V1 as [WFv1 [body1 [? H1]]].
    subst v1.
    eapply E_star; [|now eauto].

    eapply step.star_trans'.
    eapply step.star_app1. now eauto.
    eapply step.star_trans'.
    eapply step.star_app2. now eauto.
    eauto using step.step_l, step.beta, step.star_refl'.
  Qed.

End has_sem_type.

End old.