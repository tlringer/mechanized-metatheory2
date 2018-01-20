From mm Require Import util abt.

Module exprop.
  Inductive t' :=
  | abs
  | app
  | tt
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tt => []
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End exprop.

Module type.
  Inductive t :=
  | unit
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
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op exprop.abs [A.bind 1 a'] => abs (of_abt a')
    | A.op exprop.app [A.bind 0 a1; A.bind 0 a2] => app (of_abt a1) (of_abt a2)
    | A.op exprop.tt [] => tt
    | _ => var 0 (* bogus *)
    end.

  Lemma ws_to_abt : forall e, A.ws (to_abt e).
  Proof. induction e; simpl; intuition. Qed.

  Lemma of_to_abt : forall e, of_abt (to_abt e) = e.
  Proof. induction e; simpl; f_equal; auto. Qed.

  Lemma to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.
  Proof.
    induction a using A.rect'
    with (Pb := fun b => forall v,
                    A.ws_binder v b ->
                    match b with
                    | A.bind _ a => to_abt (of_abt a) = a
                    end) ; simpl; intros; f_equal; intuition;
      fold A.ws_binders in *.
    - repeat break_match; subst; simpl in *; intuition;
        repeat match goal with
               | [ H : Forall _ (_ :: _) |- _ ] => inversion H; subst; clear H
               end; simpl in *; try omega;
      repeat f_equal; eauto.
  Qed.

  Fixpoint shift c d (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else x + d)
    | abs e' => abs (shift (S c) d e')
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tt => tt
    end.

  Lemma shift_to_abt_comm : forall e c d, to_abt (shift c d e) = A.shift c d (to_abt e).
  Proof. induction e; simpl; intros c d; auto; repeat f_equal; auto. Qed.

  Fixpoint subst rho e :=
    match e with
    | var x => match nth_error rho x with
                  | Some e' => e'
                  | None => e
                  end
    | abs e' => abs (subst (var 0 :: map (shift 0 1) rho) e')
    | app e1 e2 => app (subst rho e1) (subst rho e2)
    | tt => tt
    end.


  Lemma map_shift_to_abt_comm :
    forall c d rho, map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).
  Proof.
    intros.
    rewrite !map_map.
    now erewrite map_ext by (intros; apply shift_to_abt_comm).
  Qed.

  Lemma subst_to_abt_comm : forall e rho,
      to_abt (subst rho e) = A.subst (map to_abt rho) (to_abt e).
  Proof.
    unfold t.
    induction e; simpl; intros rho; rewrite ?A.descend_0, ?A.descend_1; repeat f_equal; auto.
    - rewrite nth_error_map. break_match; auto.
    - rewrite IHe. simpl.
      now rewrite map_shift_to_abt_comm.
  Qed.

  Fixpoint wf n e :=
    match e with
    | var x => x < n
    | abs e' => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
    | tt => True
    end.

  Lemma wf_to_abt : forall e n, wf n e <-> A.wf n (to_abt e).
  Proof. induction e; simpl; firstorder. Qed.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

  Lemma identity_subst_to_abt_comm :
    forall n,
      List.map to_abt (identity_subst n) = A.identity_subst n.
  Proof.
    induction n; simpl; f_equal; auto.
    now rewrite map_shift_to_abt_comm, IHn.
  Qed.
End expr_basis.

Module expr.
  Include abt.abt_util expr_basis.
  Notation var := expr_ast.var.
  Notation abs := expr_ast.abs.
  Notation app := expr_ast.app.
  Notation tt := expr_ast.tt.
End expr.


Module has_type.
  Inductive t : list type.t -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      List.nth_error G x = Some ty ->
      t G (expr.var x) ty
  | tt : forall G,
      t G expr.tt type.unit
  | abs : forall G e ty1 ty2,
      t (ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2
  .
End has_type.


Module ctx.
  Definition t := list type.t.
End ctx.

Lemma has_type_shift :
  forall G e ty,
    has_type.t G e ty ->
    forall G1 G2 G',
      G1 ++ G2 = G ->
      has_type.t (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
Proof.
  induction 1; intros G1 G2 G' E; subst G.
  - constructor.
    do_ltb.
    + now rewrite nth_error_app1 in * by assumption.
    + rewrite !nth_error_app2 in * by omega.
      now do_app2_minus.
  - constructor.
  - cbn [expr.shift].
    constructor.
    change (ty1 :: G1 ++ G' ++ G2) with ((ty1 :: G1) ++ G' ++ G2).
    now apply IHt.
  - simpl. econstructor.
    + now apply IHt1.
    + now apply IHt2.
Qed.

Lemma has_type_shift' :
  forall G e ty G',
    has_type.t G e ty ->
    has_type.t (G' ++ G) (expr.shift 0 (List.length G') e) ty.
Proof.
  intros.
  now apply has_type_shift with (G := G) (G1 := []).
Qed.

Lemma has_type_shift_cons :
  forall G e ty ty0,
    has_type.t G e ty ->
    has_type.t (ty0 :: G) (expr.shift 0 1 e) ty.
Proof.
  intros.
  now apply has_type_shift' with (G' := [ty0]).
Qed.

Lemma has_type_subst :
  forall G e ty,
    has_type.t G e ty ->
    forall G' rho,
      List.Forall2 (has_type.t G') rho G ->
      has_type.t G' (expr.subst rho e) ty.
Proof.
  induction 1; intros G' rho F; cbn [expr.subst].
  - destruct (Forall2_nth_error_l F H) as [z [Hz Ht]].
    unfold expr.t in *.
    now rewrite Hz.
  - constructor.
  - constructor.
    apply IHt.
    constructor.
    + now constructor.
    + apply Forall2_map_l.
      apply Forall2_forall_suff_weak.
      * now erewrite Forall2_length by eauto.
      * intros.
        apply has_type_shift_cons.
        eapply (Forall2_nth_error F); eauto.
  - econstructor.
    + now apply IHt1.
    + now apply IHt2.
Qed.

Module value.
  Inductive t : expr.t -> Prop :=
  | tt : t expr.tt
  | abs : forall e, t (expr.abs e)
  .
End value.

Module step.
  Inductive t : expr.t -> expr.t -> Prop :=
  | app1  : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.app e1 e2) (expr.app e1' e2)
  | app2  : forall e1 e2 e2',
      t e2 e2' ->
      t (expr.app e1 e2) (expr.app e1 e2')
  | beta : forall e1 e2,
      t (expr.app (expr.abs e1) e2)
        (expr.subst [e2] e1)
  .
  Hint Constructors t.

  Definition star : expr.t -> expr.t -> Prop := clos_refl_trans_n1 _ t.

  Lemma step_l :
    forall e1 e2 e3,
      step.t e1 e2 ->
      step.star e2 e3 ->
      step.star e1 e3.
  Proof.
    intros e1 e2 e3 S Star.
    apply clos_rt_rtn1.
    apply clos_rtn1_rt in Star.
    eapply rt_trans; eauto using rt_step.
  Qed.

  Lemma star_app1 :
    forall e1 e1' e2,
      star e1 e1' ->
      star (expr.app e1 e2) (expr.app e1' e2).
  Proof.
    intros e1 e1' e2 Star.
    revert e2.
    induction Star; intros e2.
    - constructor.
    - econstructor; [|apply IHStar].
      eauto.
  Qed.

  Lemma star_app2 :
    forall e1 e2 e2',
      star e2 e2' ->
      star (expr.app e1 e2) (expr.app e1 e2').
  Proof.
    intros e1 e2 e2' Star.
    revert e1.
    induction Star; intros e1.
    - constructor.
    - econstructor; [|apply IHStar].
      eauto.
  Qed.

  Lemma star_trans :
    forall e1 e2 e3,
      star e1 e2 ->
      star e2 e3 ->
      star e1 e3.
  Proof.
    intros e1 e2 e3 S1 S2.
    apply clos_rtn1_rt in S1.
    apply clos_rtn1_rt in S2.
    apply clos_rt_rtn1.
    eauto using rt_trans.
  Qed.
End step.
