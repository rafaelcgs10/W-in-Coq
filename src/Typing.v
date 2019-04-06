Set Implicit Arguments.

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
Require Import SimpleTypes.
Require Import MyLtacs.

(** * Lambda term definition *)

Inductive term : Set :=
| var_t   : id -> term
| app_t   : term -> term -> term
| let_t   : id -> term -> term -> term
| lam_t   : id -> term -> term
| const_t : id -> term.

(** * Syntax-directed rule system of Damas-Milner *)

Inductive has_type : ctx -> term -> ty -> Prop :=
| const_ht : forall x G, has_type G (const_t x) (con x)
| var_ht : forall x G sigma tau, in_ctx x G = Some sigma -> is_schm_instance tau sigma ->
                            has_type G (var_t x) tau
| lam_ht : forall x G tau tau' e, has_type ((x, ty_to_schm tau) :: G) e tau' ->
                             has_type G (lam_t x e) (arrow tau tau')
| app_ht : forall G tau tau' l rho, has_type G l (arrow tau tau') ->
                               has_type G rho tau ->
                               has_type G (app_t l rho) tau'
| let_ht : forall G x e e' tau tau', has_type G e tau ->
                                has_type ((x, gen_ty tau G) :: G) e' tau' ->
                                has_type G (let_t x e e') tau'.

(*** The Great Substitution Lemma *)
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
    pose proof exists_renaming_not_concerned_with2 (gen_ty_vars tau0 G)
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

Hint Resolve has_type_is_stable_under_substitution.