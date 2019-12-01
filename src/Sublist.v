(** * The subslist relation
      This file contains the defintion of the sublist relation [is_sublist_id] and its 
      lemmas (some of them related to disjoints lists).
    *)

Set Implicit Arguments.

Require Import LibTactics.
Require Import ListIds.
Require Import Context.
Require Import Schemes.
Require Import SubstSchm.
Require Import SimpleTypes.
Require Import Subst.
Require Import MyLtacs.
Require Import Disjoints.
Require Import Arith.Arith_base.
Require Import List.

Inductive is_sublist_id : (list id) -> (list id) -> Prop := is_sublist_intro: forall (l1 l2: (list id)),
      (forall (st: id), in_list_id st l1 = true -> in_list_id st l2 = true) -> is_sublist_id l1 l2.

Hint Constructors is_sublist_id:core.

Lemma sublist_reflexivity: forall l : (list id), (is_sublist_id l l).
Proof.
  intros.
  econstructor; auto.
Qed.

Hint Resolve sublist_reflexivity:core.

Lemma nil_is_sublist : forall l: (list id), (is_sublist_id nil l).
Proof.
  intros.
  econstructor; intros; auto.
  simpl in H. inversion H.
Qed.

Hint Resolve nil_is_sublist:core.

Lemma append_sublist : forall (l l1 l2 : (list id)),
    (is_sublist_id l1 l) -> (is_sublist_id l2 l) ->
    (is_sublist_id (l1 ++ l2) l).
Proof.
  intros.
  econstructor. intros.
  apply in_list_id_or_append_inversion in H1.
  destruct H1.
  inversion H. auto.
  inversion H0. auto.
Qed.

Hint Resolve append_sublist:core.

Lemma sublist_of_append1 : forall (l l1 l2 : (list id)),
    (is_sublist_id l l1) -> (is_sublist_id l (l1 ++ l2)).
Proof.
  intros.
  econstructor. intros.
  inversion H.
  apply in_list_id_append1. auto.
Qed.

Hint Resolve sublist_of_append1:core.

Lemma sublist_of_append2 : forall (l l1 l2 : (list id)),
    (is_sublist_id l l2) -> (is_sublist_id l (l1 ++ l2)).
Proof.
  intros.
  econstructor. intros.
  inversion H.
  apply in_list_id_append2. auto.
Qed.

Hint Resolve sublist_of_append2:core.

Lemma sublist_of_append_inversion1 : forall (l l1 l2: list id),
    (is_sublist_id (l1 ++ l2) l) -> (is_sublist_id l1 l).
Proof.
  intros.
  inversion H.
  pose proof in_list_id_append1 as HH.
  econstructor.
  intros. apply H0.
  auto.
Qed.

Hint Resolve sublist_of_append_inversion1:core.

Lemma sublist_of_append_inversion2 : forall (l l1 l2: list id),
    (is_sublist_id (l1 ++ l2) l) -> (is_sublist_id l2 l).
Proof.
  intros.
  inversion H.
  pose proof in_list_id_append2 as HH.
  econstructor.
  intros. apply H0.
  auto.
Qed.

Hint Resolve sublist_of_append_inversion2:core.

Lemma in_list_id_cons_to_app : forall l i st, in_list_id st (l ++ i :: nil) = true ->
                                         in_list_id st (i::l) = true.
Proof.
  intros.
  induction l; crush.
Qed.

Hint Resolve in_list_id_cons_to_app:core.

Lemma sublist_cons_inv : forall (l l': (list id)) (i: id),
    (is_sublist_id l l') -> (in_list_id i l') = true -> (is_sublist_id (l ++ i::nil) l').
Proof.
  intros.
  econstructor.
  intros.
  inverts* H.
  apply in_list_id_cons_to_app in H1.
  simpl in H1.
  crush.
Qed.

Hint Resolve sublist_cons_inv:core.

Lemma sublist_inv1 : forall (l1 l2 : list id) (st : id), is_sublist_id l1 l2 ->
                                                    in_list_id st l1 = true ->
                                                    in_list_id st l2 = true.
intros.
inversion_clear H; auto.
Qed.

Hint Resolve sublist_inv1:core.

Lemma sublist_cons : forall (l l0: (list id)) (a: id),
    (is_sublist_id (a::l0) l) -> (is_sublist_id l0 l).
Proof.
  intros.
  econstructor.
  intros.
  inversion H. apply H1.
  mysimp.
Qed.

Hint Resolve sublist_cons:core.

Lemma disjoint_list_and_append : forall (l l1 l2: (list id)),
    (are_disjoints l1 l) -> (are_disjoints l2 l) ->
    (are_disjoints (l1 ++ l2) l).
Proof.
  unfold are_disjoints.
  intros.
  apply in_list_id_or_append_inversion in H1.
  destruct H1; auto.
Qed.

Hint Resolve disjoint_list_and_append:core.

Lemma are_disjoints_symetry : forall (l l' : (list id)),
    (are_disjoints l l') -> (are_disjoints l' l).
Proof.
  intros.
  intro. intros.
  eapply disjoint_inversion2.
  apply H. auto.
Qed.

Hint Resolve are_disjoints_symetry:core.

Lemma disjoint_sublist_bis : forall (l1 l2 l: (list id)),
    (are_disjoints l2 l1) -> (is_sublist_id l l2) -> (are_disjoints l1 l).
  intros.
  inversion H0. subst.
  apply are_disjoints_symetry.
  intro. intros.
  auto.
Qed.

Hint Resolve disjoint_sublist_bis:core.

Lemma sublist_FV_type_scheme : forall (s : substitution) (sigma : schm) (i : id),
    (in_list_id i (FV_schm sigma)) = true ->
    (is_sublist_id (ids_ty (apply_subst s (var i))) 
                       (FV_schm (apply_subst_schm s sigma))).
Proof.
  intros.
  induction sigma.
  - econstructor. intros.
    simpl in H.
    destruct (eq_id_dec i0 i); intuition.
    subst.
    assert (sc_var i = ty_to_schm (var i)). {reflexivity. }
    rewrite H1.                                           
    rewrite ty_to_subst_schm.
    rewrite FV_type_scheme_type_to_type_scheme. auto.
  - simpl in H. inversion H.
  - simpl in H. inversion H.
  - simpl in H. 
    apply in_list_id_or_append_inversion in H.
    destruct H;
      rewrite apply_subst_schm_arrow;
      simpl.
    eapply sublist_of_append1. auto.
    eapply sublist_of_append2. auto.
Qed.            

Hint Resolve sublist_FV_type_scheme:core.

Lemma sublist_FV_ctx : forall (G: ctx) (s: substitution) (i : id),
    in_list_id i (FV_ctx G) = true ->
    (is_sublist_id (ids_ty (apply_subst s (var i))) (FV_ctx (apply_subst_ctx s G))).
Proof.
  intros.
  induction G.
  - simpl in H. inversion H.
  - destruct a.
    destruct (in_list_id_or_append_inversion i (FV_schm s0) (FV_ctx G) H).
    eapply sublist_of_append1.
    simpl.
    eapply sublist_FV_type_scheme; auto.
    unfold FV_ctx.
    simpl.
    eapply sublist_of_append2.
    auto.
Qed.

Hint Resolve sublist_FV_ctx:core.

Lemma sublist_of_2_app : forall l l' l1 l2 : list id,
    is_sublist_id l1 l ->
    is_sublist_id l2 l' ->
    is_sublist_id (l1 ++ l2) (l ++ l').
Proof.
  intros.
  econstructor. intros.
  eauto.
Qed.

Hint Resolve sublist_of_2_app:core.
  