Set Implicit Arguments.

Require Import SubstSchm.
Require Import List.
Require Import ListIds.
Require Import Context.
Require Import Disjoints.
Require Import Gen.
Require Import SimpleTypes.
Require Import Subst.
Require Import Context.
Require Import MyLtacs.
Require Import Nth_error_tools.
Require Import LibTactics.


Inductive is_prefixe_free2 : list id -> list id -> list id -> Prop :=
|  prefixe_free2_intro : forall C l L : list id,
    {l1 : list id | L = l ++ l1 /\ are_disjoints C l1} -> is_prefixe_free2 C l L.

Hint Constructors is_prefixe_free2.

Lemma is_prefixe2_gen_aux : forall (l L : list id) (tau : ty) (G : ctx),
    is_prefixe_free2 (FV_ctx G) (snd (gen_ty_aux tau G l)) L ->
    is_prefixe_free2 (FV_ctx G) l L.
Proof.
  intros.
  destruct (Snd_gen_aux_with_app3 G tau l).
  destruct H0.
  inverts* H.
  destruct H2.
  destruct a.
  econstructor.
  exists (x ++ x0).
  split.
  rewrite app_assoc.
  rewrite <- H0.
  rewrite H. reflexivity.
  eauto.
Qed.

Hint Resolve is_prefixe2_gen_aux.

Lemma is_prefixe_reflexivity : forall C L : list id, is_prefixe_free2 C L L.
intros C L.
econstructor.
exists (nil: list id).
 split; auto.
 apply app_nil_end.
Qed.

Hint Resolve is_prefixe_reflexivity.

