Set Implicit Arguments.

Require Import LibTactics.
Require Import ListIds.
Require Import Subst.
Require Import SimpleTypes.
Require Import MyLtacs.
Require Import Disjoints.
Require Import Schemes.
Require Import Arith.Arith_base.
Require Import List.

(** * Context definition *)

Definition ctx : Set := list (id * schm)%type.

Fixpoint apply_subst_ctx  (s : substitution) (c : ctx) : ctx :=
  match c with
  | nil => nil
  | (x, sigma)::xs => (x, apply_subst_schm s sigma)::apply_subst_ctx s xs
  end.

(** Checks if a id is in a context *)
Fixpoint in_ctx (y : id) (G : ctx) : option schm :=
  match G with
  | nil => None
  | ((x, t)::xs) => if eq_id_dec x y then Some t else in_ctx y xs
  end.                                                          

Lemma apply_subst_ctx_nil : forall G, apply_subst_ctx nil G = G.
Proof.
  induction G; mysimp.
  destruct a. rewrite apply_subst_schm_nil. rewrite IHG. reflexivity.
Qed.

Hint Resolve apply_subst_ctx_nil.

Lemma subst_add_type_scheme : forall (G : ctx) (i : id) (s : substitution) (sigma : schm),
    apply_subst_ctx s ((i, sigma)::G) = (i,(apply_subst_schm s sigma))::(apply_subst_ctx s G).
Proof.
  intros.
  reflexivity.
Qed.

Hint Resolve subst_add_type_scheme.

Lemma apply_subst_ctx_compose : forall G s1 s2 ,
    apply_subst_ctx (compose_subst s1 s2) G = apply_subst_ctx s2 (apply_subst_ctx s1 G).
Proof.  
  induction G .
  - mysimp.
  - intros . mysimp. destruct a.
    rewrite apply_schm_compose_equiv. rewrite IHG ; auto.
Qed.

Hint Resolve apply_subst_ctx_compose.

Lemma apply_subst_ctx_eq :forall i s tau G,
    (i, apply_subst_schm s tau)::apply_subst_ctx s G =
    apply_subst_ctx s ((i, tau)::G).
Proof.
  intros. reflexivity.
Qed.

Hint Resolve apply_subst_ctx_eq.

Definition FV_ctx (G : ctx) : list id :=
  List.concat (List.map FV_schm (List.map (@snd id schm) G)). 

Lemma not_in_FV_ctx : forall (G : ctx) (st : id) (s: substitution),
    in_list_id st (img_ids s) = false ->
    in_list_id st (FV_ctx G) = false ->
    in_list_id st (FV_ctx (apply_subst_ctx s G)) = false.
Proof.
  induction G; intros.
  - reflexivity.
  - destruct a.
    unfold FV_ctx in H0. simpl in H0.
    unfold FV_ctx. simpl.
    eapply in_list_id_and_append.
    split.
    + apply in_list_id_append_inversion1 in H0.
      eapply not_in_FV_type_scheme; auto.
    + apply in_list_id_append_inversion2 in H0.
      apply IHG; auto.
Qed.

Hint Resolve not_in_FV_ctx.

(** Identity condition for apply_ctx *)
Lemma subst_ctx_when_s_disjoint_with_ctx: forall (G: ctx) (s: substitution),
    (are_disjoints (dom s) (FV_ctx G)) ->
    (apply_subst_ctx s G) = G.
Proof.
  induction G.
  - intros. reflexivity.
  - intros.
    simpl.
    destruct a.
    unfold FV_ctx in *.
    simpl in *.
    rewrite subst_schm_when_dom_s_disjoint_with_FV_schm.
    erewrite IHG.
    reflexivity.
    apply disjoint_list_and_append_inversion3 in H.
    mysimp.
    apply disjoint_list_and_append_inversion3 in H.
    mysimp.
Qed.

Hint Resolve subst_ctx_when_s_disjoint_with_ctx.
