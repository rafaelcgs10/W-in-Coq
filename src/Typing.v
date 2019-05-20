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
Require Import NonEmptyList.

(** * Pattern definition *)

Inductive pat : Set :=
| var_p : id -> pat
| const_p : id -> pat
| constr_p : id -> list pat -> pat.

(** * Lambda term definition *)

Inductive term : Set :=
| var_t   : id -> term
| app_t   : term -> term -> term
| let_t   : id -> term -> term -> term
| lam_t   : id -> term -> term
| const_t : id -> term
| case_t  : term ->  non_empty_list (pat * term) -> term.

(** * Rules for typing patterns *)

Definition not_arrow (tau : ty) : Prop :=
  match tau with
  | arrow _ _ => False
  | _ => True
  end.

Definition not_arrow_dec (tau : ty) : bool :=
  match tau with
  | arrow _ _ => false
  | _ => true
  end.

Fixpoint arguments_of_ty (tau : ty) : list ty :=
  match tau with
  | arrow tau1 tau2 => tau1::arguments_of_ty tau2
  | _ => nil
  end.

Fixpoint return_of_ty (tau : ty) : ty :=
  match tau with
  | arrow tau1 tau2 => return_of_ty tau2
  | tau' => tau'
  end.

Inductive is_constructor_schm : schm -> Prop :=
| con_is : forall x, is_constructor_schm (sc_con x)
| arrow_is : forall sigma1 sigma2, is_constructor_schm sigma1 ->
                              is_constructor_schm (sc_arrow sigma1 sigma2).

Inductive has_type_pat : ctx -> pat -> ty -> Prop:=
| const_htp : forall x G, has_type_pat G (const_p x) (con x)
| var_htp : forall x tau, has_type_pat G (var_p x) tau
| constr_htp : forall x sigma ps tau, in_ctx x G = Some sigma ->
                                 is_constructor_schm sigma ->
                                 is_schm_instance tau sigma ->
                                 has_type_pats ps tau -> 
                                 has_type_pat (constr_p x ps) (return_of_ty tau)
with
has_type_pats : list pat -> list ty -> Prop :=
| no_pat : has_type_pats nil 
| many_pat : forall p ps tau taus, has_type_pat p tau ->
                              has_type_pats ps taus  ->
                              has_type_pats (p::ps) (tau::taus).

Fixpoint get_pats (cs : non_empty_list (pat * term)) : non_empty_list pat :=
  match cs with
  | one (p, _) =>  one p
  | cons' (p, _) cs' => cons' p (get_pats cs')
  end.

Fixpoint get_terms (cs : non_empty_list (pat * term)) : non_empty_list term :=
  match cs with
  | one (_, t) =>  one t
  | cons' (_, t) cs' => cons' t (get_terms cs')
  end.

Scheme has_type_pat_mut := Minimality for has_type_pat Sort Prop
with has_type_pats_mut := Minimality for has_type_pats Sort Prop.

(** has_pat is stable under substitution *)
Lemma has_type_pat_is_stable_under_substitution : forall p s tau,
    has_type_pat p tau -> has_type_pat p (apply_subst s tau).
Proof.
  intros.
  Admitted.
  (*
  apply (has_type_pat_mut
           (fun (p'': pat) tau => forall s tau',
                has_type_pat p'' tau' -> has_type_pat p'' (apply_subst s tau'))
           (fun l (tau : ty) => forall s tau',
                has_type_pats l tau' -> has_type_pats l (apply_subst s tau'))
           ) with (p:=p) (t:=tau); intros; eauto.
  (** const case *)
  - inverts* H0.
    econstructor.
  (** var case *)
  - econstructor; eauto.
  (** list case *)
  - inverts* H3.
    apply list_htp with (tau1:=apply_subst s0 tau0).
    rewrite <- apply_subst_arrow.
    skip.
    rewrite <- apply_subst_arrow.
    eauto.
  - inverts* H2.
    econstructor.
    fold (apply_subst s0 tau0).
    eauto.
  - inverts* H4.
    econstructor.
    + fold (apply_subst s0 tau0).
      eauto.
    + fold (apply_subst s0 tau4).
      fold (apply_subst s0 tau5).
      rewrite <- apply_subst_arrow.
      eauto.
Qed.
*)
      
Hint Resolve has_type_pat_is_stable_under_substitution.

(** has_patterns is stable under substitution *)
(*
Lemma has_type_patterns_is_stable_under_substitution : forall l s tau,
    has_type_pats l tau -> has_type_pats l (apply_subst s tau).
Proof.
Admitted.
  induction l.
  - intros. inverts H.
    econstructor.
    auto.
  - intros. 
    inverts* H.
    econstructor.
    auto.
    auto.
Qed.    

Hint Resolve has_type_patterns_is_stable_under_substitution.
*)

(** * Syntax-directed rule system of Damas-Milner *)

Inductive has_type : ctx -> term -> ty -> Prop :=
| const_ht : forall x G, has_type G (const_t x) (con x)
| var_ht : forall x G sigma tau, in_ctx x G = Some sigma ->
                            is_schm_instance tau sigma ->
                            has_type G (var_t x) tau
| lam_ht : forall x G tau tau' e, has_type ((x, ty_to_schm tau) :: G) e tau' ->
                             has_type G (lam_t x e) (arrow tau tau')
| app_ht : forall G tau tau' l r, has_type G l (arrow tau tau') ->
                               has_type G r tau ->
                               has_type G (app_t l r) tau'
| let_ht : forall G x e e' tau tau', has_type G e tau ->
                                has_type ((x, gen_ty tau G) :: G) e' tau' ->
                                has_type G (let_t x e e') tau'
| case_ht : forall G e tau tau' cs, has_type G e tau ->
                               has_type_cases G cs tau tau' ->
                               has_type G (case_t e cs) tau'
with
has_type_cases : ctx -> non_empty_list (pat * term) -> ty -> ty -> Prop :=
| one_term : forall G p e tau tau', has_type_pat p tau ->
                                  has_type G e tau' -> 
                                  has_type_cases G (one (p, e)) tau tau'
| many_terms : forall G pe tau tau' cs, has_type_cases G (one pe) tau tau' -> 
                                   has_type_cases G cs tau tau' ->
                                   has_type_cases G (cons' pe cs) tau tau'.

Scheme has_type_mut := Minimality for has_type Sort Prop
with has_type_cases_mut := Minimality for has_type_cases Sort Prop.

Check has_type_mut.

(** * The Great Substitution Lemma *)

(** has_type is stable under substitution *)
Lemma has_type_is_stable_under_substitution : forall e s tau G,
    has_type G e tau -> has_type (apply_subst_ctx s G) e (apply_subst s tau).
Proof.
  intros.
  apply (has_type_mut
           (fun (G' : ctx) (e' : term) (tau' : ty) => forall s tau G,
                         has_type G e' tau -> has_type (apply_subst_ctx s G) e' (apply_subst s tau))
           (fun  (G' : ctx) (l' : non_empty_list (pat * term)) (tau' tau'' : ty) => forall s tau1 tau2 G,
              has_type_cases G l' tau1 tau2 -> has_type_cases (apply_subst_ctx s G) l' (apply_subst s tau1) (apply_subst s tau2))
           ) with (c:=G) (t0:=tau); intros.
  (** const case *)
  - inverts* H0.
    econstructor.
  (** var case *)
  - skip.
    (*
    inversion H2.
    subst.
    rename G into G', G1 into G.
    rename s into s', s0 into s.
    rename tau into tau', tau1 into tau.
    rename i into i', x into i.
    econstructor.
    + induction G; simpl in *; mysimp.
      destruct a.
      mysimp.
      apply IHG.
      econstructor.
      apply H2.
      assumption.
      assumption.
    + unfold is_schm_instance in *.
      destruct H4.
      eapply subst_inst_subst_type in H1.
      exists (map_apply_subst_ty s x).
      apply H1.
*)
  (** lambda case *)
  - inverts* H2.
    rewrite apply_subst_arrow.
    econstructor.
    rewrite <- ty_to_subst_schm.
    rewrite apply_subst_ctx_eq.
    auto.
    (** app case *)
  - skip.
    (*
    rename l into e1, rho into e2.
    rename s into s1, s0 into s.
    rename H0 into IHe1, H1 into IHe2.
    inverts* H2.
    rename tau into tau'', tau1 into tau.
    rename tau0 into tau1, tau2 into tau0.
    apply app_ht with (tau:=apply_subst s tau0).
    rewrite <- apply_subst_arrow.
    apply IHe1.
    assumption.
    apply IHe2.
    assumption.
*)
    (** let case *)
  - skip.
    (*
    inverts* H2.
    rename e0 into e1, e' into e2.
    rename s into s', s0 into s.
    rename tau into tau'', tau1 into tau.
    rename tau0 into tau0', tau2 into tau0.
    rename G into G', G1 into G.
    rename x into i.
    rename H0 into IHe1, H1 into IHe2.
    destruct (exists_renaming_not_concerned_with (gen_ty_vars tau0 G)
         (FV_ctx G) (FV_subst s)) as [rho].
    inversion r.
    subst.
    pose proof (gen_ty_in_subst_ctx G s (apply_subst (rename_to_subst rho) tau0)) as hip.
    pose proof (renaming_not_concerned_with_gen_vars) as hip2.
    apply hip2 in r as r'.
    apply hip in r' as r''.
    pose proof (subst_ctx_when_s_disjoint_with_ctx G (rename_to_subst rho)) as Hdis. 
    pose proof (apply_subst_ctx_compose G (rename_to_subst rho) s) as Hcompo.
    apply let_ht with (tau:= apply_subst s (apply_subst (rename_to_subst rho) tau0)).
    erewrite <- Hdis.
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
*)
  (** case case *)
  - induction cs.
    + inverts* H4.
      econstructor.
      eapply H1.
      apply H8.
      auto.
    + inverts* H4.
      econstructor.
      eapply H1; eauto.
      auto.
    (** terms one case *)
  - inverts* H3.
    econstructor; eauto.
    (** terms many case *)
  - inverts* H4.
    econstructor; eauto.
  - auto.
  - auto.
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

(*
Lemma has_type_pat_cons_commm : forall G i j  sigma1 sigma2 tau,
    i <> j ->
    has_type_pat ((i, sigma1) :: (j, sigma2) :: G) (var_p i) tau ->
    has_type_pat ((j, sigma2) :: (i, sigma1) :: G) (var_p i) tau.
Proof.
  intros.
  inversion H0.
  subst.
  

Lemma has_type_pat_var_ctx_diff : forall (i j : id) (G : ctx) (tau : ty) (sigma : schm),
    i <> j -> has_type_pat (var_p i) tau -> has_type_pat ((j, sigma) :: G) (var_p i) tau.
Proof.
  intros.
  inversion_clear H0.
  econstructor.
  econstructor; crush.
Qed.

Hint Resolve has_type_pat_var_ctx_diff.
*)