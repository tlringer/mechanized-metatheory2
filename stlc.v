(* 
 * Reenactment of commit e7ef8a4cafcd21bd17cbf5cd8004e991577a5a26#diff-5e2396245414cb01f14b3b3629da114aL345
 *)

From mm Require Import util abt.

(* Old stlc.v before any changes *)
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


Module has_type.
  Inductive t : list type.t -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      List.nth_error G x = Some ty ->
      t G (expr.var x) ty
  | tt : forall G,
      t G expr.tt type.bool
  | ff : forall G,
      t G expr.ff type.bool
  | abs : forall G e ty1 ty2,
      t (ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2
  | If : forall G e1 e2 e3 ty,
      t G e1 type.bool ->
      t G e2 ty -> 
      t G e3 ty ->
      t G (expr.If e1 e2 e3) ty
  .

  Lemma wf :
    forall G e ty,
      t G e ty ->
      expr.wf (List.length G) e.
  Proof.
    induction 1; simpl in *; intuition.
    pose proof nth_error_Some G x. intuition congruence.
  Qed.

  Lemma shift :
    forall G e ty,
      t G e ty ->
      forall G1 G2 G',
        G1 ++ G2 = G ->
        t (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
  Proof.
    induction 1; intros G1 G2 G' E; subst G.
    - constructor.
      do_ltb.
      + now rewrite nth_error_app1 in * by assumption.
      + rewrite !nth_error_app2 in * by omega.
        now do_app2_minus.
    - constructor.
    - constructor.
    - cbn [expr.shift].
      constructor.
      change (ty1 :: G1 ++ G' ++ G2) with ((ty1 :: G1) ++ G' ++ G2).
      now apply IHt.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.

  Lemma shift' :
    forall G e ty G',
      t G e ty ->
      t (G' ++ G) (expr.shift 0 (List.length G') e) ty.
  Proof.
    intros.
    now apply shift with (G := G) (G1 := []).
  Qed.

  Lemma shift_cons :
    forall G e ty ty0,
      t G e ty ->
      t (ty0 :: G) (expr.shift 0 1 e) ty.
  Proof.
    intros.
    now apply shift' with (G' := [ty0]).
  Qed.

  Lemma subst :
    forall G e ty,
      t G e ty ->
      forall G' rho,
        List.Forall2 (t G') rho G ->
        t G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros G' rho F; cbn [expr.subst].
    - destruct (Forall2_nth_error2 F H) as [z [Hz Ht]].
      unfold expr.t in *.
      simpl.
      now rewrite Hz.
    - constructor.
    - constructor.
    - constructor.
      apply IHt.
      constructor.
      + now constructor.
      + apply Forall2_map_l.
        apply Forall2_forall_suff_weak.
        * now erewrite Forall2_length by eauto.
        * intros.
          apply shift_cons.
          eapply (Forall2_nth_error F); eauto.
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.
End has_type.

Module ctx.
  Definition t := list type.t.
End ctx.

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
      auto. (* we change to auto to be consistent *)
  Qed.

  Lemma star_If :
    forall e1 e1' e2 e3,
      star e1 e1' ->
      star (expr.If e1 e2 e3) (expr.If e1' e2 e3).
  Proof.
    intros e1 e1' e2 e3 Star.
    revert e2 e3.
    induction Star; intros e2 e3.
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

  Lemma star_refl :
    forall e,
      star e e.
  Proof.
    constructor.
  Qed.

  Hint Resolve star_app2 star_app1 star_refl.

  Lemma value :
    forall v,
      value.t v ->
      forall e',
        step.t v e' ->
        False.
  Proof.
    induction 1; intros e' Step; inversion Step; subst.
  Qed.

  Lemma star_value :
    forall v e',
      value.t v ->
      step.star v e' ->
      e' = v.
  Proof.
    intros v e' Val Star.
    apply clos_rtn1_rt in Star.
    apply clos_rt_rt1n in Star.
    inversion Star; subst; auto.
    exfalso; eauto using value.
  Qed.
End step.

Module context.
  Inductive t :=
  | hole
  | abs : t -> t
  | app1 : t -> expr.t -> t
  | app2 : expr.t -> t -> t
  | If1 : t -> expr.t -> expr.t -> t
  | If2 : expr.t -> t -> expr.t -> t
  | If3 : expr.t -> expr.t -> t -> t
  .

  Fixpoint plug (C : t) (e : expr.t) : expr.t :=
    match C with
    | hole => e
    | abs C' => expr.abs (plug C' e)
    | app1 C1 e2 => expr.app (plug C1 e) e2
    | app2 e1 C2 => expr.app e1 (plug C2 e)
    | If1 C1 e2 e3 => expr.If (plug C1 e) e2 e3
    | If2 e1 C2 e3 => expr.If e1 (plug C2 e) e3
    | If3 e1 e2 C3 => expr.If e1 e2 (plug C3 e)
    end.
End context.

Module context_has_type.
  Inductive t : list type.t -> context.t -> list type.t -> type.t -> type.t -> Prop :=
  | hole : forall G ty, t G context.hole G ty ty
  | abs : forall G' C G ty ty1' ty2',
      t (ty1' :: G') C (ty1' :: G) ty ty2' ->
      t G' (context.abs C) (ty1' :: G) ty (type.arrow ty1' ty2')
  | app1 : forall G' C G ty ty1' ty2' e,
      t G' C G ty (type.arrow ty1' ty2') ->
      has_type.t G' e ty1' ->
      t G' (context.app1 C e) G ty ty2'
  | app2 : forall G' C G ty ty1' ty2' e,
      has_type.t G' e (type.arrow ty1' ty2') ->
      t G' C G ty ty1' ->
      t G' (context.app2 e C) G ty ty2'
  | If1 : forall G' C1 G ty ty' e2 e3,
      t G' C1 G ty type.bool ->
      has_type.t G' e2 ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If1 C1 e2 e3) G ty ty'
  | If2 : forall G' C2 G ty ty' e1 e3,
      has_type.t G' e1 type.bool ->
      t G' C2 G ty ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If2 e1 C2 e3) G ty ty'
  | If3 : forall G' C3 G ty ty' e1 e2,
      has_type.t G' e1 type.bool ->
      has_type.t G' e2 ty' ->
      t G' C3 G ty ty' ->
      t G' (context.If3 e1 e2 C3) G ty ty'
  .

  Theorem plug :
    forall G' C G ty ty',
      t G' C G ty ty' ->
      forall e,
        has_type.t G e ty ->
        has_type.t G' (context.plug C e) ty'.
  Proof.
    induction 1; intros e0 HT0; cbn [context.plug]; try assumption;
      apply IHt in HT0; econstructor; eauto.
  Qed.
End context_has_type.

Module context_equiv.
  Definition t G e1 e2 ty : Prop :=
    forall C v1 v2,
      context_has_type.t [] C G ty type.bool ->
      step.star (context.plug C e1) v1 ->
      value.t v1 ->
      step.star (context.plug C e2) v2 ->
      value.t v2 ->
      v1 = v2.
End context_equiv.

End old.

(* Stlc.v after adding a single valuet to the beta case. *)
Module add_valuet_beta.

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


Module has_type.
  Inductive t : list type.t -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      List.nth_error G x = Some ty ->
      t G (expr.var x) ty
  | tt : forall G,
      t G expr.tt type.bool
  | ff : forall G,
      t G expr.ff type.bool
  | abs : forall G e ty1 ty2,
      t (ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2
  | If : forall G e1 e2 e3 ty,
      t G e1 type.bool ->
      t G e2 ty -> 
      t G e3 ty ->
      t G (expr.If e1 e2 e3) ty
  .

  Lemma wf :
    forall G e ty,
      t G e ty ->
      expr.wf (List.length G) e.
  Proof.
    induction 1; simpl in *; intuition.
    pose proof nth_error_Some G x. intuition congruence.
  Qed.

  Lemma shift :
    forall G e ty,
      t G e ty ->
      forall G1 G2 G',
        G1 ++ G2 = G ->
        t (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
  Proof.
    induction 1; intros G1 G2 G' E; subst G.
    - constructor.
      do_ltb.
      + now rewrite nth_error_app1 in * by assumption.
      + rewrite !nth_error_app2 in * by omega.
        now do_app2_minus.
    - constructor.
    - constructor.
    - cbn [expr.shift].
      constructor.
      change (ty1 :: G1 ++ G' ++ G2) with ((ty1 :: G1) ++ G' ++ G2).
      now apply IHt.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.

  Lemma shift' :
    forall G e ty G',
      t G e ty ->
      t (G' ++ G) (expr.shift 0 (List.length G') e) ty.
  Proof.
    intros.
    now apply shift with (G := G) (G1 := []).
  Qed.

  Lemma shift_cons :
    forall G e ty ty0,
      t G e ty ->
      t (ty0 :: G) (expr.shift 0 1 e) ty.
  Proof.
    intros.
    now apply shift' with (G' := [ty0]).
  Qed.

  Lemma subst :
    forall G e ty,
      t G e ty ->
      forall G' rho,
        List.Forall2 (t G') rho G ->
        t G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros G' rho F; cbn [expr.subst].
    - destruct (Forall2_nth_error2 F H) as [z [Hz Ht]].
      unfold expr.t in *.
      simpl.
      now rewrite Hz.
    - constructor.
    - constructor.
    - constructor.
      apply IHt.
      constructor.
      + now constructor.
      + apply Forall2_map_l.
        apply Forall2_forall_suff_weak.
        * now erewrite Forall2_length by eauto.
        * intros.
          apply shift_cons.
          eapply (Forall2_nth_error F); eauto.
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.
End has_type.

Module ctx.
  Definition t := list type.t.
End ctx.

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
      value.t e2 ->
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
      auto. (* we change to auto to be consistent *)
  Qed.

  Lemma star_If :
    forall e1 e1' e2 e3,
      star e1 e1' ->
      star (expr.If e1 e2 e3) (expr.If e1' e2 e3).
  Proof.
    intros e1 e1' e2 e3 Star.
    revert e2 e3.
    induction Star; intros e2 e3.
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

  Lemma star_refl :
    forall e,
      star e e.
  Proof.
    constructor.
  Qed.

  Hint Resolve star_app2 star_app1 star_refl.

  Lemma value :
    forall v,
      value.t v ->
      forall e',
        step.t v e' ->
        False.
  Proof.
    induction 1; intros e' Step; inversion Step; subst.
  Qed.

  Lemma star_value :
    forall v e',
      value.t v ->
      step.star v e' ->
      e' = v.
  Proof.
    intros v e' Val Star.
    apply clos_rtn1_rt in Star.
    apply clos_rt_rt1n in Star.
    inversion Star; subst; auto.
    exfalso; eauto using value.
  Qed.
End step.

Module context.
  Inductive t :=
  | hole
  | abs : t -> t
  | app1 : t -> expr.t -> t
  | app2 : expr.t -> t -> t
  | If1 : t -> expr.t -> expr.t -> t
  | If2 : expr.t -> t -> expr.t -> t
  | If3 : expr.t -> expr.t -> t -> t
  .

  Fixpoint plug (C : t) (e : expr.t) : expr.t :=
    match C with
    | hole => e
    | abs C' => expr.abs (plug C' e)
    | app1 C1 e2 => expr.app (plug C1 e) e2
    | app2 e1 C2 => expr.app e1 (plug C2 e)
    | If1 C1 e2 e3 => expr.If (plug C1 e) e2 e3
    | If2 e1 C2 e3 => expr.If e1 (plug C2 e) e3
    | If3 e1 e2 C3 => expr.If e1 e2 (plug C3 e)
    end.
End context.

Module context_has_type.
  Inductive t : list type.t -> context.t -> list type.t -> type.t -> type.t -> Prop :=
  | hole : forall G ty, t G context.hole G ty ty
  | abs : forall G' C G ty ty1' ty2',
      t (ty1' :: G') C (ty1' :: G) ty ty2' ->
      t G' (context.abs C) (ty1' :: G) ty (type.arrow ty1' ty2')
  | app1 : forall G' C G ty ty1' ty2' e,
      t G' C G ty (type.arrow ty1' ty2') ->
      has_type.t G' e ty1' ->
      t G' (context.app1 C e) G ty ty2'
  | app2 : forall G' C G ty ty1' ty2' e,
      has_type.t G' e (type.arrow ty1' ty2') ->
      t G' C G ty ty1' ->
      t G' (context.app2 e C) G ty ty2'
  | If1 : forall G' C1 G ty ty' e2 e3,
      t G' C1 G ty type.bool ->
      has_type.t G' e2 ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If1 C1 e2 e3) G ty ty'
  | If2 : forall G' C2 G ty ty' e1 e3,
      has_type.t G' e1 type.bool ->
      t G' C2 G ty ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If2 e1 C2 e3) G ty ty'
  | If3 : forall G' C3 G ty ty' e1 e2,
      has_type.t G' e1 type.bool ->
      has_type.t G' e2 ty' ->
      t G' C3 G ty ty' ->
      t G' (context.If3 e1 e2 C3) G ty ty'
  .

  Theorem plug :
    forall G' C G ty ty',
      t G' C G ty ty' ->
      forall e,
        has_type.t G e ty ->
        has_type.t G' (context.plug C e) ty'.
  Proof.
    induction 1; intros e0 HT0; cbn [context.plug]; try assumption;
      apply IHt in HT0; econstructor; eauto.
  Qed.
End context_has_type.

Module context_equiv.
  Definition t G e1 e2 ty : Prop :=
    forall C v1 v2,
      context_has_type.t [] C G ty type.bool ->
      step.star (context.plug C e1) v1 ->
      value.t v1 ->
      step.star (context.plug C e2) v2 ->
      value.t v2 ->
      v1 = v2.
End context_equiv.

End add_valuet_beta.

(* Stlc.v after another single valuet to the app2 case. *)
Module add_valuet_app2.

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


Module has_type.
  Inductive t : list type.t -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      List.nth_error G x = Some ty ->
      t G (expr.var x) ty
  | tt : forall G,
      t G expr.tt type.bool
  | ff : forall G,
      t G expr.ff type.bool
  | abs : forall G e ty1 ty2,
      t (ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2
  | If : forall G e1 e2 e3 ty,
      t G e1 type.bool ->
      t G e2 ty -> 
      t G e3 ty ->
      t G (expr.If e1 e2 e3) ty
  .

  Lemma wf :
    forall G e ty,
      t G e ty ->
      expr.wf (List.length G) e.
  Proof.
    induction 1; simpl in *; intuition.
    pose proof nth_error_Some G x. intuition congruence.
  Qed.

  Lemma shift :
    forall G e ty,
      t G e ty ->
      forall G1 G2 G',
        G1 ++ G2 = G ->
        t (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
  Proof.
    induction 1; intros G1 G2 G' E; subst G.
    - constructor.
      do_ltb.
      + now rewrite nth_error_app1 in * by assumption.
      + rewrite !nth_error_app2 in * by omega.
        now do_app2_minus.
    - constructor.
    - constructor.
    - cbn [expr.shift].
      constructor.
      change (ty1 :: G1 ++ G' ++ G2) with ((ty1 :: G1) ++ G' ++ G2).
      now apply IHt.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.

  Lemma shift' :
    forall G e ty G',
      t G e ty ->
      t (G' ++ G) (expr.shift 0 (List.length G') e) ty.
  Proof.
    intros.
    now apply shift with (G := G) (G1 := []).
  Qed.

  Lemma shift_cons :
    forall G e ty ty0,
      t G e ty ->
      t (ty0 :: G) (expr.shift 0 1 e) ty.
  Proof.
    intros.
    now apply shift' with (G' := [ty0]).
  Qed.

  Lemma subst :
    forall G e ty,
      t G e ty ->
      forall G' rho,
        List.Forall2 (t G') rho G ->
        t G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros G' rho F; cbn [expr.subst].
    - destruct (Forall2_nth_error2 F H) as [z [Hz Ht]].
      unfold expr.t in *.
      simpl.
      now rewrite Hz.
    - constructor.
    - constructor.
    - constructor.
      apply IHt.
      constructor.
      + now constructor.
      + apply Forall2_map_l.
        apply Forall2_forall_suff_weak.
        * now erewrite Forall2_length by eauto.
        * intros.
          apply shift_cons.
          eapply (Forall2_nth_error F); eauto.
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.
End has_type.

Module ctx.
  Definition t := list type.t.
End ctx.

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
      value.t e2 ->
      t (expr.app (expr.abs e1) e2)
        (expr.subst [e2] e1)
  | app1  : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.app e1 e2) (expr.app e1' e2)
  | app2  : forall e1 e2 e2',
      value.t e1 ->
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

  (* 
   * As expected, star_app2 breaks.
   * Like James, we add the premise here.
   *)
  Lemma star_app2 :
    forall e1 e2 e2',
      value.t e1 -> (* new _ : value.t e1 *)
      star e2 e2' ->
      star (expr.app e1 e2) (expr.app e1 e2').
  Proof.
    intros e1 e2 e2' Val1 Star. (* new Val1 : value.t eq *)
    revert e1 Val1. (* need to revert this too, now *)
    induction Star; intros e1 Val1.
    - constructor.
    - econstructor; [|apply IHStar];
      auto. (* two cases now, note the semicolon *)
  Qed.

  (* IHStar : forall e1 : expr.t,
         value.t e1 -> star (expr_ast.app e1 e2) (expr_ast.app e1 y) *)

  (* IHStar : forall e1 : expr.t,
         star (expr_ast.app e1 e2) (expr_ast.app e1 y) *)

  Definition patch:
    forall e1 e2 e2',
      value.t e1 ->
      star e2 e2' ->
      (value.t e1 -> star (expr_ast.app e1 e2) (expr_ast.app e1 e2')) ->
      star (expr_ast.app e1 e2) (expr_ast.app e1 e2').
  Proof.
    intros. apply H1. apply H.
  Qed. 
  (* PUMPKIN PATCH should be able to find the above automatically, but generalized *)

  Definition patch2:
    forall e1 e2 e2' P,
      value.t e1 ->
      (value.t e1 -> P (expr_ast.app e1 e2) (expr_ast.app e1 e2')) ->
      P (expr_ast.app e1 e2) (expr_ast.app e1 e2').
  Proof.
    intros e1 e2 e2' P H H0. apply H0. apply H.
  Qed. 

Definition patch_by_hand (e1 e2 e2' : expr.t) (Val1 : value.t e1) :=
  (fun (y z : expr.t) (H : step.t y z) (_ : clos_refl_trans_n1 expr.t step.t e2 y)
       (IHStar : forall (e3 : expr.t), value.t e3 -> step.star (expr_ast.app e3 e2) (expr_ast.app e3 y)) 
       (e3 : expr.t) 
       (Val2 : value.t e3) =>
    IHStar e3 Val2).   (* Note how star is removed *)  

(*
add_valuet_beta.step.star_app2 = 
  fun (e1 e2 e2' : expr.t) (Star : step.star e2 e2') =>
    clos_refl_trans_n1_ind
      expr.t
      step.t
      e2
      (fun (e2'0 : expr.t) =>
        forall (e3 : expr.t),
        step.star (expr_ast.app e3 e2) (expr_ast.app e3 e2'0))
      (fun (e3 : expr.t) =>
        rtn1_refl expr.t step.t (expr_ast.app e3 e2))
      (fun (y z : expr.t) (H : step.t y z) (_ : clos_refl_trans_n1 expr.t step.t e2 y)
           (IHStar : forall (e3 : expr.t), step.star (expr_ast.app e3 e2) (expr_ast.app e3 y))
           (e3 : expr.t) =>
        Relation_Operators.rtn1_trans
          expr.t
          step.t
          (expr_ast.app e3 e2)
          (expr_ast.app e3 y)
          (expr_ast.app e3 z)
          (step.app2 e3 y z H)
          (IHStar e3))
      e2' 
      Star
      e1
: forall (e1 e2 e2' : expr.t),
    step.star e2 e2' -> step.star (expr_ast.app e1 e2) (expr_ast.app e1 e2')
*)

(*
add_valuet_beta.step.star_app2 = 
  fun (e1 e2 e2' : expr.t) (Val1 : value.t e1) (Star : step.star e2 e2') =>
    clos_refl_trans_n1_ind
      expr.t
      step.t
      e2
      (fun (e2'0 : expr.t) =>
        forall (e3 : expr.t),
          value.t e3 ->
          step.star (expr_ast.app e3 e2) (expr_ast.app e3 e2'0))
      (fun (e3 : expr.t) =>
        rtn1_refl expr.t step.t (expr_ast.app e3 e2))
      (fun (y z : expr.t) (H : step.t y z) (_ : clos_refl_trans_n1 expr.t step.t e2 y)
           (IHStar : forall (e3 : expr.t), value.t e3 -> step.star (expr_ast.app e3 e2) (expr_ast.app e3 y))
           c
        Relation_Operators.rtn1_trans
          expr.t
          step.t
          (expr_ast.app e3 e2)
          (expr_ast.app e3 y)
          (expr_ast.app e3 z)
          (step.app2 e3 y z H)
          (IHStar e3))
      e2' 
      Star
      e1
: forall (e1 e2 e2' : expr.t),
    step.star e2 e2' -> step.star (expr_ast.app e1 e2) (expr_ast.app e1 e2')


add_valuet_app2.step.star_app2 =
  fun (e1 e2 e2' : expr.t) (Val1 : value.t e1) (Star : step.star e2 e2') =>
    clos_refl_trans_n1_ind
      expr.t
      step.t
      e2
      (fun (e2'0 : expr.t) =>
        forall (e3 : expr.t),
          value.t e3 ->
          step.star (expr_ast.app e3 e2) (expr_ast.app e3 e2'0))
      (fun (e3 : expr.t) (_ : value.t e3) =>
        rtn1_refl expr.t step.t (expr_ast.app e3 e2))
      (fun (y z : expr.t) (H : step.t y z) (_ : clos_refl_trans_n1 expr.t step.t e2 y)
           (IHStar : forall (e3 : expr.t), value.t e3 -> step.star (expr_ast.app e3 e2) (expr_ast.app e3 y))
           (e3 : expr.t)
           (Val2 : value.t e3) =>
        Relation_Operators.rtn1_trans
          expr.t
          step.t
          (expr_ast.app e3 e2)
          (expr_ast.app e3 y)
          (expr_ast.app e3 z)
          (step.app2 e3 y z Val2 H) 
          (IHStar e3 Val2))
      e2'
      Star
      e1
      Val1
: forall (e1 e2 e2' : expr.t),
    value.t e1 ->
    step.star e2 e2' -> step.star (expr_ast.app e1 e2) (expr_ast.app e1 e2')
*)

  Lemma star_app2' :
    forall e1 e2 e2',
      value.t e1 -> (* new _ : value.t e1 *)
      star e2 e2' ->
      star (expr.app e1 e2) (expr.app e1 e2').
  Proof.
    intros e1 e2 e2' Val1 Star. (* new Val1 : value.t eq *)
    revert e1 Val1. (* need to revert this too, now *)
    induction Star; intros e1 Val1.
    - constructor.
    - econstructor; [|apply (patch_by_hand e1 e2 y Val1 y z H Star IHStar e1 Val1)].
      auto.
  Qed.

  (* OK, so we can patch the inductive hypothesis, basically! *)
  (* Then we know exactly what arguments to apply it to in order. *)

  (* TODO define patch that transforms IH to a new IH and rewrite proof 
     with that. *)

  (* TODO write star_app2 again with some variant of patch *)

  Lemma star_If :
    forall e1 e1' e2 e3,
      star e1 e1' ->
      star (expr.If e1 e2 e3) (expr.If e1' e2 e3).
  Proof.
    intros e1 e1' e2 e3 Star.
    revert e2 e3.
    induction Star; intros e2 e3.
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

  Lemma star_refl :
    forall e,
      star e e.
  Proof.
    constructor.
  Qed.

  Hint Resolve (*star_app2*) star_app1 star_refl.

  Lemma value :
    forall v,
      value.t v ->
      forall e',
        step.t v e' ->
        False.
  Proof.
    induction 1; intros e' Step; inversion Step; subst.
  Qed.

  Lemma star_value :
    forall v e',
      value.t v ->
      step.star v e' ->
      e' = v.
  Proof.
    intros v e' Val Star.
    apply clos_rtn1_rt in Star.
    apply clos_rt_rt1n in Star.
    inversion Star; subst; auto.
    exfalso; eauto using value.
  Qed.
End step.

Module context.
  Inductive t :=
  | hole
  | abs : t -> t
  | app1 : t -> expr.t -> t
  | app2 : expr.t -> t -> t
  | If1 : t -> expr.t -> expr.t -> t
  | If2 : expr.t -> t -> expr.t -> t
  | If3 : expr.t -> expr.t -> t -> t
  .

  Fixpoint plug (C : t) (e : expr.t) : expr.t :=
    match C with
    | hole => e
    | abs C' => expr.abs (plug C' e)
    | app1 C1 e2 => expr.app (plug C1 e) e2
    | app2 e1 C2 => expr.app e1 (plug C2 e)
    | If1 C1 e2 e3 => expr.If (plug C1 e) e2 e3
    | If2 e1 C2 e3 => expr.If e1 (plug C2 e) e3
    | If3 e1 e2 C3 => expr.If e1 e2 (plug C3 e)
    end.
End context.

Module context_has_type.
  Inductive t : list type.t -> context.t -> list type.t -> type.t -> type.t -> Prop :=
  | hole : forall G ty, t G context.hole G ty ty
  | abs : forall G' C G ty ty1' ty2',
      t (ty1' :: G') C (ty1' :: G) ty ty2' ->
      t G' (context.abs C) (ty1' :: G) ty (type.arrow ty1' ty2')
  | app1 : forall G' C G ty ty1' ty2' e,
      t G' C G ty (type.arrow ty1' ty2') ->
      has_type.t G' e ty1' ->
      t G' (context.app1 C e) G ty ty2'
  | app2 : forall G' C G ty ty1' ty2' e,
      has_type.t G' e (type.arrow ty1' ty2') ->
      t G' C G ty ty1' ->
      t G' (context.app2 e C) G ty ty2'
  | If1 : forall G' C1 G ty ty' e2 e3,
      t G' C1 G ty type.bool ->
      has_type.t G' e2 ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If1 C1 e2 e3) G ty ty'
  | If2 : forall G' C2 G ty ty' e1 e3,
      has_type.t G' e1 type.bool ->
      t G' C2 G ty ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If2 e1 C2 e3) G ty ty'
  | If3 : forall G' C3 G ty ty' e1 e2,
      has_type.t G' e1 type.bool ->
      has_type.t G' e2 ty' ->
      t G' C3 G ty ty' ->
      t G' (context.If3 e1 e2 C3) G ty ty'
  .

  Theorem plug :
    forall G' C G ty ty',
      t G' C G ty ty' ->
      forall e,
        has_type.t G e ty ->
        has_type.t G' (context.plug C e) ty'.
  Proof.
    induction 1; intros e0 HT0; cbn [context.plug]; try assumption;
      apply IHt in HT0; econstructor; eauto.
  Qed.
End context_has_type.

Module context_equiv.
  Definition t G e1 e2 ty : Prop :=
    forall C v1 v2,
      context_has_type.t [] C G ty type.bool ->
      step.star (context.plug C e1) v1 ->
      value.t v1 ->
      step.star (context.plug C e2) v2 ->
      value.t v2 ->
      v1 = v2.
End context_equiv.

End add_valuet_app2.

(*
 * Effectively, we can think of the addition to the theorem
 * star_app2 as defining the patch for that case.
 *)

(*
 * The commented out terms below are reduced to the same namespace,
 * and equivalent modules (expr_ast.t and expr.t) are rewritten as the same type
 * for clarity of differencing.
 *)

(*
old.step.star_app2 = 
  fun (e1 e2 e2' : expr.t) (Star : step.star e2 e2') =>
    clos_refl_trans_n1_ind
      expr.t
      step.t
      e2
      (fun (e2'0 : expr.t) =>
        forall (e3 : expr.t),
          step.star (expr_ast.app e3 e2) (expr_ast.app e3 e2'0))
      (fun (e3 : expr.t) =>
        rtn1_refl expr.t step.t (expr_ast.app e3 e2))
      (fun (y z : expr.t) (H : step.t y z) (_ : clos_refl_trans_n1 expr.t step.t e2 y)
           (IHStar : forall (e3 : expr.t), step.star (expr_ast.app e3 e2) (expr_ast.app e3 y)) 
           (e3 : expr.t) =>
         Relation_Operators.rtn1_trans
           expr.t
           step.t
           (expr_ast.app e3 e2)
           (expr_ast.app e3 y)
           (expr_ast.app e3 z)
           (step.app2 e3 y z H) 
           (IHStar e3))
      e2'
      Star
      e1
: forall (e1 e2 e2' : expr.t),
    step.star e2 e2' -> step.star (expr_ast.app e1 e2) (expr_ast.app e1 e2')
 *)

Print add_valuet_beta.step.star_app2.

(*
add_valuet_beta.step.star_app2 = 
  fun (e1 e2 e2' : expr.t) (Star : step.star e2 e2') =>
    clos_refl_trans_n1_ind
      expr.t
      step.t
      e2
      (fun (e2'0 : expr.t) =>
        forall (e3 : expr.t),
        step.star (expr_ast.app e3 e2) (expr_ast.app e3 e2'0))
      (fun (e3 : expr.t) =>
        rtn1_refl expr.t step.t (expr_ast.app e3 e2))
      (fun (y z : expr.t) (H : step.t y z) (_ : clos_refl_trans_n1 expr.t step.t e2 y)
           (IHStar : forall (e3 : expr.t), step.star (expr_ast.app e3 e2) (expr_ast.app e3 y))
           (e3 : expr.t) =>
        Relation_Operators.rtn1_trans
          expr.t
          step.t
          (expr_ast.app e3 e2)
          (expr_ast.app e3 y)
          (expr_ast.app e3 z)
          (step.app2 e3 y z H)
          (IHStar e3))
      e2' 
      Star
      e1
: forall (e1 e2 e2' : expr.t),
    step.star e2 e2' -> step.star (expr_ast.app e1 e2) (expr_ast.app e1 e2')
*)

Print add_valuet_app2.step.star_app2.

(*
add_valuet_app2.step.star_app2 =
  fun (e1 e2 e2' : expr.t) (Val1 : value.t e1) (Star : step.star e2 e2') =>
    clos_refl_trans_n1_ind
      expr.t
      step.t
      e2
      (fun (e2'0 : expr.t) =>
        forall (e3 : expr.t),
          value.t e3 ->
          step.star (expr_ast.app e3 e2) (expr_ast.app e3 e2'0))
      (fun (e3 : expr.t) (_ : value.t e3) =>
        rtn1_refl expr.t step.t (expr_ast.app e3 e2))
      (fun (y z : expr.t) (H : step.t y z) (_ : clos_refl_trans_n1 expr.t step.t e2 y)
           (IHStar : forall (e3 : expr.t), value.t e3 -> step.star (expr_ast.app e3 e2) (expr_ast.app e3 y))
           (e3 : expr.t)
           (Val2 : value.t e3) =>
        Relation_Operators.rtn1_trans
          expr.t
          step.t
          (expr_ast.app e3 e2)
          (expr_ast.app e3 y)
          (expr_ast.app e3 z)
          (step.app2 e3 y z Val2 H) 
          (IHStar e3 Val2))
      e2'
      Star
      e1
      Val1
: forall (e1 e2 e2' : expr.t),
    value.t e1 ->
    step.star e2 e2' -> step.star (expr_ast.app e1 e2) (expr_ast.app e1 e2')
*)

(*
 * Changes to star_app2:
 *
 * 1. New hypothesis Val1 : value.t e1
 * 2. In definition of P passed to induction principle clos_refl_trans_n1_ind,
 *    a new hypothesis of type value.t e3, but an otherwise identical case
 * 3. In base case, a new hypothesis of type value.t e3, but an otherwise identical case
 * 4. A new hypothesis of type value.t e3 in the induction hypothesis IHStar
 * 5. A new hypothesis Val2 : value.t e3 in the inductive case
 * 6. In the body of the inductive case, sticking Val2 into the application of step.app2
 * 7. Applying the new hypothesis Val1 at the very end
 * 8. A new hypothesis in of type value.t e1 in the type itself
 *)

(*
 * In other words, to construct a new (app2 e3) from an old (app2 e3),
 * the ornament needs to take in an element of type (value.t e3).
 * The patch for the ornament constructs a value.t e3 from the context.
 *
 * So this isn't quite as interesting as the list case, but what happens here is that
 * we construct value.t e3 by extending the context. We extend the context
 * of the property itself to get there, so this change happens universally.
 * This is a kind of change we can always make when we extend an inductive type in this way,
 * though it won't always give us an interesting new theorem. It's kind of analogous to this:
 *)

Definition extend_nat (T : Type) (n : nat) : Type :=
  nat_rect
    (fun (_ : nat) => Type)
    unit
    (fun (_ : nat) (IH : Type) =>
      T)
    n.

Definition extend_nat_next (T : Type) : Type :=
  forall (n : nat),
    extend_nat T n ->
    T ->
    extend_nat T (S n).

Theorem extend_nat_next_impl :
  forall (T : Type) (n : nat),
    extend_nat T n ->
    T ->
    extend_nat T (S n).
Proof.
  intros T n ext t. apply t.
Defined.

Theorem extend_nat_impl:
  forall (T : Type) (n : nat),
    extend_nat_next T ->
    T ->
    extend_nat T n.
Proof.
  intros T n next t. induction n.
  - apply tt.
  - apply next.
    + apply IHn.
    + apply t.
Defined.

Theorem patch_S (T : Type) :
  forall (n : nat),
    extend_nat T (S n) ->
    extend_nat T n ->
    (extend_nat T n -> list T) ->
    list T.
Proof.
  intros n ext_S ext IH. apply cons.
  - apply ext_S.
  - apply IH. apply ext.
Defined.

Theorem patch_O (T : Type) :
  extend_nat T O ->
  list T.
Proof.
  intros ext. apply nil. 
Defined.

Eval compute in (fun (T : Type) => patch_O T tt).

Eval compute in
  (fun (T : Type) (t1 : T) =>
    patch_S T O t1 tt (patch_O T)). 

Theorem foo:
  forall (T : Type) (t1 t2 : T),
    list T.
Proof.
  intros. apply (patch_S T 1).
  - apply t1.
  - apply t2.
  - intros ext. apply (patch_S T O).
    + apply ext.
    + apply tt.
    + intros ext2. apply patch_O. apply ext2.
Defined.

Print foo.

Eval compute in
  (fun (T : Type) (t2 t1 : T) =>
    patch_S T 1 t2 t1
      (fun (ext : extend_nat T 1) =>
         patch_S T 0 ext tt
           (fun (ext2 : extend_nat T 0) => patch_O T ext2))).

Theorem foo'_inv:
  forall (T : Type) (l : list T),
    nat.
Proof.
  intros T l. induction l.
  - apply O.
  - apply (S IHl).
Defined.

(*
 * I got really sidetracked, go figure.
 * Ignore all of this for now.
 *)

(*
 * As a proof this works, but computationally this sucks because it adds the same
 * t to each inductive case.
 *
 * However, if we're proving something about properties, this might
 * actually make sense. Let's pick some property that lists preserve about nats.
 *)

Definition P (n : nat) :=
  0 <= n.

Inductive le_list (T : Type) (l : list T) : list T -> Prop :=
| le_l : le_list T l l
| le_cons : forall (l' : list T) (t : T),
           le_list T l l' ->
           le_list T l (cons t l').

Definition Q (T : Type) (t : T) (l : list T) :=
  le_list T nil l.

Theorem bar:
  forall (n : nat),
    P n.
Proof.
  intros. induction n; unfold P. 
  - apply le_n. 
  - apply le_S. apply IHn.
Defined.

Theorem baz:
  forall (T : Type) (t : T) (l : list T),
    Q T t l.
Proof.
  intros. induction l; unfold Q.
  - apply le_l.
  - apply le_cons. apply IHl.  
Defined.

Print bar.

(*
bar = 
fun n : nat =>
nat_ind (fun n0 : nat => P n0) (le_n 0)
  (fun (n0 : nat) (IHn : P n0) => le_S 0 n0 IHn) n
     : forall n : nat, P n
 *)

Print baz. 

(*
 baz = 
fun (T : Type) (t : T) (l : list T) =>
list_ind (fun l0 : list T => Q T t l0) (le_l T [])
  (fun (a : T) (l0 : list T) (IHl : Q T t l0) =>
   le_cons T [] l0 a IHl) l
     : forall (T : Type) (t : T) (l : list T), Q T t l
*)

(*
 * We don't need a patch at the tactic level for this one because
 * it's obvious, but probably would if it showed up as a later premise,
 * which is what happens for James' proof.
 *)

(*
 * This just means that expressing the computational patch for lists to nats
 * that actually takes a different t for each case is harder than this problem.
 * But for now, maybe we can just solve this problem.
 *)

(*
 * OK, but given that people are working at the tactic level, now
 * what?
 *
 * We could define this entire new function for them, but that's lame.
 *
 * Probably, honestly, an ad-hoc approach is the best for this.
 * In other words, use ornaments to search, but don't actually
 * define them in Coq, or ever. Ornaments just tell us
 * how to search and apply?
 *
 * That is, here, we can tell from the difference in types
 * that we are looking for an ornament that extends that case.
 *
 * So, TODO next time:
 * 1. Define a patch term that gets you through with the same proof that you can apply in the case.
 * 2. After, determine how to reconcile that with the theory of ornaments.
 *)

(*
 * The patch needs to somehow capture the extra case and figure out
 * how to extract the right term from the context to handle it.
 * In this case it won't be any more efficient than auto, probably,
 * but whatever.
 *)
