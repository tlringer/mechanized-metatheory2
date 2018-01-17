Require Export List Arith Omega.
Require Export Relations.Relations.

Export ListNotations.
Set Implicit Arguments.

Hint Constructors Forall Forall2.

Ltac break_match :=
  match goal with
  | [  |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
  | [ H : context [ match ?X with _ => _ end ] |- _ ] => destruct X eqn:?
  end.

Lemma nth_error_map :
  forall A B (f : A -> B) n l,
    nth_error (map f l) n =
    match nth_error l n with
    | None => None
    | Some x => Some (f x)
    end.
Proof.
  induction n; intros; destruct l; simpl in *; auto.
Qed.

Lemma Forall_map :
  forall A B (f : A -> B) P l,
    Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  intros A B f P l.
  split.
  - induction l; simpl; intuition.
    inversion H; subst. constructor; auto.
  - induction 1; simpl; constructor; auto.
Qed.

Lemma Forall2_nth_error_l :
  forall {A B} {P : A -> B -> Prop} {l1 l2 x y},
    List.Forall2 P l1 l2 ->
    List.nth_error l2 x = Some y ->
    exists z,
      List.nth_error l1 x = Some z /\
      P z y
.
Proof.
  intros A B P l1 l2 x y F.
  revert x y.
  induction F as [|a b l1' l2' HR F']; intros x y NE; destruct x; simpl in *; try discriminate.
  - inversion NE. subst. eauto.
  - auto.
Qed.

Lemma Forall2_nth_error_r :
  forall {A B} {P : A -> B -> Prop} {l1 l2 x y},
    List.Forall2 P l1 l2 ->
    List.nth_error l1 x = Some y ->
    exists z,
      List.nth_error l2 x = Some z /\
      P y z
.
Proof.
  intros A B P l1 l2 x y F.
  revert x y.
  induction F as [|a b l1' l2' HR F']; intros x y NE; destruct x; simpl in *; try discriminate.
  - inversion NE. subst. eauto.
  - auto.
Qed.

Lemma Forall2_nth_error :
  forall {A B} {P : A -> B -> Prop} {l1 l2 x y z},
    List.Forall2 P l1 l2 ->
    List.nth_error l1 x = Some y ->
    List.nth_error l2 x = Some z ->
    P y z
.
Proof.
  intros A B P l1 l2 x y z F.
  revert x y z.
  induction F as [|a b l1' l2' HR F']; intros x y z NEy NEz;
    destruct x; simpl in *; try discriminate.
  - congruence.
  - eauto.
Qed.

Lemma Forall2_map_l :
  forall A B (P : A -> B -> Prop) A' (f : A' -> A) l1 l2,
    List.Forall2 (fun x => P (f x)) l1 l2 ->
    List.Forall2 P (List.map f l1) l2
.
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma Forall2_forall_suff_weak :
  forall A B (P : A -> B -> Prop) l1 l2,
    length l1 = length l2 ->
    (forall x y z,
        List.nth_error l1 x = Some y -> 
        List.nth_error l2 x = Some z ->
        P y z) ->
    List.Forall2 P l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros L HP; try omega; constructor.
  - now apply HP with (x := 0).
  - apply IHl1.
    + congruence.
    + intros x y z NE1 NE2.
      now apply HP with (x := (S x)).
Qed.

Lemma nth_error_app1 :
  forall A (l1 l2 : list A) x,
    x < List.length l1 ->
    nth_error (l1 ++ l2) x = nth_error l1 x
.
Proof.
  induction l1; intros l2 x H; simpl.
  - inversion H.
  - destruct x.
    + reflexivity.
    + simpl in *.
      apply IHl1.
      omega.
Qed.

Lemma nth_error_app2 :
  forall A (l1 l2 : list A) x,
    List.length l1 <= x ->
    nth_error (l1 ++ l2) x = nth_error l2 (x - List.length l1)
.
Proof.
  induction l1; intros l2 x H; destruct x; simpl in *; auto.
  - omega.
  - now rewrite IHl1 by omega.
Qed.

Lemma Forall_nth :
  forall A (P : A -> Prop) l n x,
    Forall P l ->
    nth_error l n = Some x ->
    P x.
Proof.
  intros A P l n x F NE.
  revert n x NE.
  induction F; simpl; intros n y NE; destruct n; inversion NE; subst; eauto.
Qed.

Lemma Forall2_length :
  forall A B (P : A -> B -> Prop) l1 l2,
    Forall2 P l1 l2 ->
    length l1 = length l2.
Proof.
  induction 1; simpl; auto using f_equal.
Qed.

Section pair_eq_dec.
  Variable A B : Type.
  Hypothesis A_eq_dec : forall (x y : A), {x = y}+{x <> y}.
  Hypothesis B_eq_dec : forall (x y : B), {x = y}+{x <> y}.

  Lemma pair_eq_dec : forall p p' : A * B, {p = p'} + {p <> p'}.
  Proof. decide equality. Defined.
End pair_eq_dec.

Lemma Forall_from_nth :
  forall A (P : A -> Prop) l,
    (forall n x, nth_error l n = Some x -> P x) ->
    Forall P l.
Proof.
  induction l; intros H; constructor.
  - now apply H with (n := 0).
  - apply IHl.
    intros n x Hnx.
    now apply H with (n := (S n)).
Qed.

Lemma Forall2_map :
  forall A B A' B' (P : A -> B -> Prop) (f : A' -> A) (g : B' -> B) l1 l2,
    Forall2 P (map f l1) (map g l2) <-> Forall2 (fun x y => P (f x) (g y)) l1 l2.
Proof.
  intros A B A' B' P f g l1 l2.
  split.
  - revert l2.
    induction l1; destruct l2; simpl; intros F; inversion F; subst; constructor; auto.
  - induction 1; simpl; constructor; auto.
Qed.

Lemma Forall2_impl :
  forall A B (P Q : A -> B -> Prop) l1 l2,
    (forall a b, P a b -> Q a b) ->
    Forall2 P l1 l2 ->
    Forall2 Q l1 l2.
Proof.
  intros A B P Q l1 l2 H F.
  induction F; constructor; auto.
Qed.

Lemma app_comm_cons' :
  forall A xs (y : A) zs,
    xs ++ y :: zs = (xs ++ [y]) ++ zs.
Proof.
  intros.
  now rewrite app_ass.
Qed.

Lemma Forall_app :
  forall A (P : A -> Prop) l1 l2,
    Forall P (l1 ++ l2) <-> (Forall P l1 /\ Forall P l2).
Proof.
  induction l1; simpl; intros l2; intuition;
    try match goal with
    | [ H : Forall _ (_ :: _) |- _ ] => inversion H; subst; clear H
    end; firstorder.
Qed.

Ltac do_ltb :=
  match goal with
  | [ |- context [ if ?x <? ?y then _ else _ ] ] =>
    destruct (Nat.ltb_spec x y)
  end.
Ltac do_app2_minus :=
  match goal with
  | [  |- context [ ?x + ?r2 - ?r1 - ?r2 ] ] =>
    replace (x + r2 - r1 - r2)
    with (x - r1) by omega
  end.

Ltac do_nth_error_Some :=
  match goal with
  | [  |- context [ nth_error ?l ?n] ] => pose proof nth_error_Some l n
  | [ H : context [ nth_error ?l ?n] |- _ ] => pose proof nth_error_Some l n
  end.