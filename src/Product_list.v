(** * The product list
      This file contains defintions and lemmas about [product_list], which computes 
      a substitution from a list of id and a list of types of the same length. 
      This function is used in the lemmas 
      [inst_subst_to_subst_aux] and [more_general_ctx_disjoint_prefix_apply_inst] 
      in the Moregeneral file. *)

Set Implicit Arguments.

Require Import List.
Require Import Sublist.
Require Import ListIds.
Require Import Context.
Require Import Typing.
Require Import Gen.
Require Import SimpleTypes.
Require Import Schemes.
Require Import Subst.
Require Import SubstSchm.
Require Import MyLtacs.
Require Import Nth_error_tools.
Require Import LibTactics.

(** This creates a substitution from a list of id and a list of types of the same length. *)
Fixpoint product_list (l1 : list id) (l2 : list ty) : option substitution :=
  match l1 with
  | nil =>  Some nil
  | st :: l'1 => match l2 with
                | nil => None
                | t :: l'2 => match product_list l'1 l'2 with
                             | None => None
                             | Some s => Some ((st, t) :: s)
                             end
                end
  end.

Lemma domain_product : forall (l : list id) (is_s : inst_subst) (phi : substitution),
    product_list l is_s = Some phi -> dom phi = l.
Proof.
  induction l. crush.
  destruct is_s. crush.
  intros. 
  simpl in *.
  cases (product_list l is_s).
  inverts* H.
  simpl.
  erewrite IHl; eauto.
  inverts* H.
Qed.  

Lemma image_by_product2 : forall (l : list id) (is_s : inst_subst) (st : id) 
                            (n0 : id) (phi : substitution) (tau : ty),
    index_list_id st l = Some n0 ->
    product_list l is_s = Some phi ->
    nth_error is_s n0 = Some tau -> apply_subst phi (var st) = tau.
Proof.
  induction l; unfold index_list_id. crush.
  intros.
  simpl in *.
  destruct (eq_id_dec a st).
  inverts* H.
  destruct is_s.
  inversion H0.
  subst.
  simpl in H1. inverts* H1.
  cases (product_list l is_s).
  inverts* H0.
  crush.
  inversion H0.
  destruct is_s.
  inversion H0.
  cases (product_list l is_s).
  inverts* H0.
  crush.
  eapply IHl.
  apply index_aux1 in H.
  unfold index_list_id. apply H.
  apply Eq.
  destruct n0. simpl in *.
  inverts* H1. destruct is_s.
  assert (False). { eapply index_aux_false with (n := 1) (m := 0); eauto. } contradiction.
  assert (False). { eapply index_aux_false with (n := 1) (m := 0); eauto. } contradiction.
  simpl. eauto.
  inversion H0.
Qed.

Hint Resolve image_by_product2.

Lemma product_for_le_length : forall (l1 : list id) (l2 : list ty),
    length l1 <= length l2 -> exists s, product_list l1 l2 = Some s.
Proof.
  induction l1; crush.
  destruct l2; crush. 
  edestruct IHl1; eauto.
  apply le_S_n in H.
  apply H.
  rewrite H0.
  exists ((a, t)::x).
  reflexivity.
Qed.

Hint Resolve product_for_le_length.

(** *)
Lemma product_list_exists : forall (tau : ty) (G : ctx) (is_s : inst_subst),
    max_gen_vars (gen_ty tau G) <= length is_s ->
    exists s, product_list (snd (gen_ty_aux tau G nil)) is_s = Some s.
Proof.
  intros.
  apply product_for_le_length.
  rewrite length_snd_gen_aux.
  crush.
Qed.
