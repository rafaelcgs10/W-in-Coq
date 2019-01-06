Set Implicit Arguments.

Require Import ListIds.
Require Import Unify.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.

Require Import LibTactics.

Definition are_disjoints (l l' : list id) : Prop :=
forall (x : id), (in_list_id x l) = true -> (in_list_id x l') = false.

Lemma are_disjoints_cons_inversion : forall a b l1 l2, are_disjoints (a::l1) (b::l2) -> are_disjoints l1 l2.
Proof.
  intros.
  unfold are_disjoints in *.
  intros.
  simpl in H.
  specialize H with (x:=x).
  destruct (eq_id_dec a x); 
  destruct (eq_id_dec b x);
  auto; intuition.
Qed.


Lemma are_disjoints_cons_l : forall a l1 l2, are_disjoints (a::l1) l2 -> are_disjoints l1 l2.
Proof.
  intros.
  unfold are_disjoints in *.
  intros.
  simpl in H.
  specialize H with (x:=x).
  destruct (eq_id_dec a x).
  auto.
  auto.
Qed.


Lemma are_disjoints_cons_diff : forall  a b l1 l2, are_disjoints (a::l1) (b::l2) -> a <> b.
Proof.
  intros. intro.
  unfold are_disjoints in H.
  specialize H with (x:=a).
  simpl in H.
  rewrite H0 in H.
  destruct (eq_id_dec b b); intuition.
Qed.

Lemma are_disjoints_cons : forall l1 l2 x y, are_disjoints l1 l2 -> y <> x ->
                                        in_list_id x l2 = false ->
                                        in_list_id y l1 = false ->
                                        are_disjoints (x::l1) (y::l2).
Proof.
  intros.
  unfold are_disjoints in *.
  intros.
  simpl.
  destruct (eq_id_dec y x0).
  - subst.
    simpl in H3.
    destruct (eq_id_dec x x0).
    intuition.
    rewrite  <- H2.
    rewrite  <- H3.
    reflexivity.
  - simpl in H3.
    destruct (eq_id_dec x x0).
    * subst. assumption.
    * apply H. assumption.
Qed.

Lemma disjoint_inversion2: forall (l l': (list id)) (x: id),
    are_disjoints l l' -> in_list_id x l' = true -> in_list_id x l = false.
Proof.
  intros.
  unfold are_disjoints in H.
  induction l'.
  inversion H0.
  assert(forall x, in_list_id x l = true -> in_list_id x l' = false).
  { intros. apply H in H1 as H1'. simpl in H1'. destruct (eq_id_dec a x0).
    inversion H1'. auto. }
  apply Bool.not_true_is_false.
  intro.
  specialize H with (x:=x).
  simpl in H, H0.
  destruct (eq_id_dec a x).
  intuition.
  intuition.
  apply H1 in H2.
  rewrite H0 in H2.
  inversion H2.
Qed.

Lemma disjoint_list_and_append_inversion1: forall (l l1 l2 : list id),
    (are_disjoints l (l1++l2) ) -> (are_disjoints l l1).
Proof.
  intros.
  unfold are_disjoints in *.
  intros.
  apply H in H0.
  apply in_list_id_append_inversion1 in H0.
  apply H0.
Qed.

Lemma disjoint_list_and_append_inversion2: forall (l l1 l2 : list id),
    (are_disjoints l (l1++l2) ) -> (are_disjoints l l2).
Proof.
  intros.
  unfold are_disjoints in *.
  intros.
  apply H in H0.
  apply in_list_id_append_inversion2 in H0.
  assumption.
Qed.

Lemma disjoint_list_and_append_inversion3: forall (l l1 l2 : (list id)),
    (are_disjoints l (l1++l2) ) -> (are_disjoints l l1) /\ (are_disjoints l l2).
Proof.
  intros.
  split.
  eapply disjoint_list_and_append_inversion1.
  apply H.
  eapply disjoint_list_and_append_inversion2.
  apply H.
Qed.
