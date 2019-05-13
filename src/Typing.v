(** * The typing rules
      This file contains the defintion typing rules of the Damas-Milner type system in
      a syntax-direct version and the great substitution lemma.
    *)

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

(** * Pattern definition *)

Inductive pat : Set :=
| var_p : id -> pat
| const_p : id -> pat.

(** * Lambda term definition *)

Inductive term : Set :=
| var_t   : id -> term
| app_t   : term -> term -> term
| let_t   : id -> term -> term -> term
| lam_t   : id -> term -> term
| const_t : id -> term
| case_t  : term ->  list (pat * term) -> term.

Inductive has_type_pat : ctx -> pat -> ty -> Prop:=
| const_htp : forall x G, has_type_pat G (const_p x) (con x)
| var_htp : forall x G sigma tau, in_ctx x G = Some sigma -> is_schm_instance tau sigma ->
                            has_type_pat G (var_p x) tau.

Inductive has_type_patterns : ctx -> list pat -> ty -> Prop :=
| one_pattern : forall G p tau, has_type_pat G p tau ->
                           has_type_patterns G (p::nil) tau
| many_pattern : forall G p ps tau, has_type_pat G p tau ->
                               has_type_patterns G ps tau ->
                               has_type_patterns G (p::ps) tau.

(** * Syntax-directed rule system of Damas-Milner *)

Fixpoint get_pats (c : list (pat * term)) : list pat :=
  match c with
  | nil => nil
  | (p, _)::c' => p::get_pats c'
  end.

Fixpoint get_terms (c : list (pat * term)) : list term :=
  match c with
  | nil => nil
  | (_, t)::c' => t::get_terms c'
  end.


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
                                has_type G (let_t x e e') tau'
| case_ht : forall G e tau tau' cs, has_type G e tau ->
                               has_type_patterns G (get_pats cs) tau ->
                               has_type_terms G (get_terms cs) tau' ->
                               has_type G (case_t e cs) tau'
  with has_type_terms : ctx -> list term -> ty -> Prop :=
       | one_term : forall G e tau, has_type G e tau ->
                                  has_type_terms G (e::nil) tau
       | many_terms : forall G e tau es, has_type G e tau -> 
                                         has_type_terms G es tau ->
                                         has_type_terms G (e::es) tau.

Scheme has_type_mut := Induction for has_type Sort Prop
with has_type_terms_mut := Induction for has_type_terms Sort Prop.

(** * The Great Substitution Lemma *)

(** has_pat is stable under substitution *)
Lemma has_type_pat_is_stable_under_substitution : forall e s G tau,
    has_type_pat G e tau -> has_type_pat (apply_subst_ctx s G) e (apply_subst s tau).
Proof.
  induction e.
  (** var case *)
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
  (** const case *)
  - intros. inversion H.
    subst.
    econstructor.
Qed.

Hint Resolve has_type_pat_is_stable_under_substitution.

(** has_patterns is stable under substitution *)
Lemma has_type_patterns_is_stable_under_substitution : forall l s G tau,
    has_type_patterns G l tau -> has_type_patterns (apply_subst_ctx s G) l (apply_subst s tau).
Proof.
  induction l.
  - intros. inverts H.
  - intros. 
    inverts* H.
    econstructor.
    auto.
    econstructor.
    auto.
    auto.
Qed.    

Hint Resolve has_type_patterns_is_stable_under_substitution.
Lemma has_type_is_stable_under_substitution_aux1 : forall l s G tau,
    (forall e', has_type G e' tau -> has_type (apply_subst_ctx s G) e' (apply_subst s tau)) ->
    has_type_terms G l tau -> has_type_terms (apply_subst_ctx s G) l (apply_subst s tau).
Proof.
  induction l.
  - intros.
    inverts* H0.
  - intros.
    inverts* H0.
    econstructor; eauto.
    econstructor; eauto.
Qed.
      

(** has_type is stable under substitution *)
Lemma has_type_is_stable_under_substitution_aux : forall e s G tau,
    (forall l, has_type_terms G l tau -> has_type_terms (apply_subst_ctx s G) l (apply_subst s tau) ) /\
    (has_type G e tau -> has_type (apply_subst_ctx s G) e (apply_subst s tau)).
Proof.
  induction e.
  (** var case *)
  - intros.
    split; intros.
    {
      - inverts* H0.
        econstructor; eauto.
        econstructor; eauto.
    }
    inversion H.
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
  (** app case *)
  - intros. 
    split; intros.
    {
      induction l.
      - inverts* H0.
      - inverts* H0.
        econstructor; auto.
        econstructor; auto.
    }
    inversion_clear H.
    apply app_ht with (tau:=apply_subst s tau0).
    rewrite <- apply_subst_arrow.
    edestruct IHe1; eauto.
    edestruct IHe2; eauto.
  (** let case *)
  - intros. 
    split; intros.
    {
      induction l.
      - inverts* H0.
      - inverts* H0.
        econstructor; auto.
        econstructor; auto.
    }
    inversion_clear H.
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
    edestruct IHe1.
    erewrite <- top.
    apply H6.
    edestruct IHe1.
    apply H8.
    assumption.
    rewrite dom_rename_to_subst.
    rewrite H2.
    apply free_and_bound_are_disjoints.
    rewrite <- r''.
    rewrite apply_subst_ctx_eq.
    edestruct IHe2.
    apply H6.
    erewrite <- gen_ty_renaming.
    assumption.
    apply r.
  (** lam case *)
  - intros. 
    split; intros.
    {
      induction l.
      - inverts* H0.
      - inverts* H0.
        econstructor; auto.
        econstructor; auto.
    }
    inversion H. subst. rewrite apply_subst_arrow.
    econstructor. rewrite <- ty_to_subst_schm.
    rewrite apply_subst_ctx_eq.
    edestruct IHe.
    apply H1.
    assumption.
  (** const case *)
  - intros. 
    split; intros.
    {
      induction l.
      - inverts* H0.
      - inverts* H0.
        econstructor; auto.
        econstructor; auto.
    }
    inversion H.
    subst.
    econstructor.
  (** case case *)
  - intros. 
    split; intros.
    {
      induction l0.
      - inverts* H0.
      - inverts* H0.
        econstructor; auto.
        econstructor; auto.
    }
    inverts* H.
    edestruct IHe.
    econstructor.
    apply H0.
    apply H2.
    auto.
    + inverts* H.
      simpl in *.
      inverts* H4.
    + inverts* H.
      apply case_ht with (tau:= apply_subst s tau0). 
      * edestruct IHe.
        eapply H0.
        auto.
      * auto.
      * destruct a.
        simpl.
        econstructor.
        edestruct IHe.
        apply H.
        intros.
        econstructor.
        edestruct IHe.
        eapply H.
        intros.
        auto.
Qed.

Hint Resolve has_type_is_stable_under_substitution.

Lemma has_type_var_ctx_diff : forall (i j : id) (G : ctx) (tau : ty) (sigma : schm),
    i <> j -> has_type G (var_t i) tau -> has_type ((j, sigma) :: G) (var_t i) tau.
Proof.
  intros.
  inversion_clear H0.
 econstructor; crush.
Qed.

Hint Resolve has_type_var_ctx_diff.

