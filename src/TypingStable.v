(** * The typing sustitution lemma
      This file contains the great substitution lemma.
    *)

Set Implicit Arguments.

Require Import SimpleTypes.
Require Import SimpleTypesNotations.
Require Import LibTactics.
Require Import Sublist.
Require Import Context.
Require Import ListIds.
Require Import Schemes.
Require Import SubstSchm.
Require Import Rename.
Require Import Disjoints.
Require Import Subst.
Require Import Gen.
Require Import Arith.Arith_base.
Require Import List.
Require Import MyLtacs.
Require Import Typing.

(** * The Great Substitution Lemma *)
(** has_type is stable under substitution *)
Lemma has_type_is_stable_under_substitution : forall e s G tau,
    has_type G e tau -> has_type (apply_subst_ctx s G) e (apply_subst s tau).
Proof.
  induction e.
  - intros. inversion H.
    subst.
    econstructor.
    + induction G; simpl in *; mysimp.
      destruct a.
      mysimp.
      apply IHG.
      econstructor.
      apply H1.
      assumption.
      assumption.
    + unfold is_schm_instance in *.
      destruct H3.
      eapply subst_inst_subst_type in H0.
      exists (map_apply_subst_ty s x).
      apply H0.
  - intros. 
    inversion H.
    subst.
    apply app_ht with (tau:=apply_subst s tau0).
    rewrite <- apply_subst_arrow.
    apply IHe1.
    assumption.
    apply IHe2.
    assumption.
  - intros. 
    inversion H.
    subst.
    pose proof exists_renaming_not_concerned_with (gen_ty_vars tau0 G)
         (FV_ctx G) (FV_subst s)  as lol.
    destruct lol as [rho].
    inversion r.
    subst.
    pose proof (gen_ty_in_subst_ctx G s (apply_subst (rename_to_subst rho) tau0)) as hip.
    pose proof (renaming_not_concerned_with_gen_vars ) as hip2.
    apply hip2 in r as r'.
    apply hip in r' as r''.
    pose proof (subst_ctx_when_s_disjoint_with_ctx G (rename_to_subst rho)) as top. 
    pose proof (apply_subst_ctx_compose G (rename_to_subst rho) s) as top2.
    apply let_ht with (tau:= apply_subst s (apply_subst (rename_to_subst rho) tau0)).
    erewrite <- top.
    eapply IHe1.
    eapply IHe1.
    assumption.
    rewrite dom_rename_to_subst.
    rewrite H1.
    apply free_and_bound_are_disjoints.
    rewrite <- r''.
    rewrite apply_subst_ctx_eq.
    eapply IHe2.
    erewrite <- gen_ty_renaming.
    assumption.
    apply r.
  - intros. inversion H. subst. rewrite apply_subst_arrow.
    econstructor. rewrite <- ty_to_subst_schm. rewrite apply_subst_ctx_eq. apply IHe.
    assumption.
  - intros. inversion H.
    subst.
    econstructor.
Qed.

Hint Resolve has_type_is_stable_under_substitution:core.

Lemma has_type_var_ctx_diff : forall (i j : id) (G : ctx) (tau : ty) (sigma : schm),
    i <> j -> has_type G (var_t i) tau -> has_type ((j, sigma) :: G) (var_t i) tau.
Proof.
  intros.
  inversion_clear H0.
 econstructor; crush.
Qed.

Hint Resolve has_type_var_ctx_diff:core.

