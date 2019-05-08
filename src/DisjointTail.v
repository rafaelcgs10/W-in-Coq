(** * The Disjoint tail
      This file contains defintions and lemmas about [is_disjoint_with_some_tail], which computes 
      a substitution from a list of id and a list of types of the same length. 
      This function is used in the lemmas 
      [inst_subst_to_subst_aux] and [more_general_ctx_disjoint_prefix_apply_inst] 
      in the Moregeneral file. *)

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
Require Import NthErrorTools.
Require Import LibTactics.


Inductive is_disjoint_with_some_tail : list id -> list id -> list id -> Prop :=
|  prefixe_free_intro : forall C l L : list id,
    {l1 : list id | L = l ++ l1 /\ are_disjoints C l1} -> is_disjoint_with_some_tail C l L.

Hint Constructors is_disjoint_with_some_tail.

Lemma is_prefixe_gen_aux : forall (l L : list id) (tau : ty) (G : ctx),
    is_disjoint_with_some_tail (FV_ctx G) (snd (gen_ty_aux tau G l)) L ->
    is_disjoint_with_some_tail (FV_ctx G) l L.
Proof.
  intros.
  destruct (exists_snd_gen_aux_app G tau l).
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

Hint Resolve is_prefixe_gen_aux.

Lemma is_prefixe_reflexivity : forall C L : list id, is_disjoint_with_some_tail C L L.
intros C L.
econstructor.
exists (nil: list id).
 split; auto.
 apply app_nil_end.
Qed.

Hint Resolve is_prefixe_reflexivity.

