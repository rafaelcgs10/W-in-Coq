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

Inductive pat : Type :=
| var_p : id -> pat
| constr_p : id -> pats -> pat
with pats : Type :=
     | no_pats : pats
     | some_pats : pat -> pats -> pats.

(** * Lambda term definition *)

Inductive term : Set :=
| var_t   : id -> term
| app_t   : term -> term -> term
| let_t   : id -> term -> term -> term
| lam_t   : id -> term -> term
| case_t  : term ->  cases -> term
with cases : Set :=
 | one_case : pat -> term -> cases
 | many_cases : pat -> term -> cases -> cases.

(** * Rules for typing patterns *)

Inductive is_constructor_schm : schm -> Prop :=
| con_is : forall x, is_constructor_schm (sc_con x)
| appl_is : forall tau1 tau2, is_constructor_schm (sc_appl tau1 tau2)
| arrow_is : forall sigma1 sigma2, is_constructor_schm sigma2 ->
                              is_constructor_schm (sc_arrow sigma1 sigma2).

Fixpoint return_of_ty (tau : ty) : ty :=
  match tau with
  | arrow tau1 tau2 => return_of_ty tau2
  | tau' => tau'
  end.
                    
Inductive has_type_pat : ctx -> pat -> ty -> Prop:=
| var_htp : forall x G tau, has_type_pat G (var_p x) tau
| constr_htp : forall G x sigma ps tau, in_ctx x G = Some sigma ->
                                 is_constructor_schm sigma ->
                                 is_schm_instance tau sigma ->
                                 has_type_pats G ps tau -> 
                                 has_type_pat G (constr_p x ps) (return_of_ty tau)
with
has_type_pats : ctx -> pats -> ty -> Prop :=
| no_pat_con : forall i G, has_type_pats G no_pats (con i) 
| no_pat_appl : forall tau1 tau2 G, has_type_pats G no_pats (appl tau1 tau2) 
| many_pat : forall p ps tau1 tau2 G, has_type_pat G p tau1 ->
                                    has_type_pats G ps tau2 ->
                                    has_type_pats G (some_pats p ps) (arrow tau1 tau2).

Scheme has_type_pat_mut := Minimality for has_type_pat Sort Prop
with has_type_pats_mut := Minimality for has_type_pats Sort Prop.

Lemma in_ctx_stable_is_under_substitution : forall G s sigma x,
    in_ctx x G = Some sigma -> in_ctx x (apply_subst_ctx s G) = Some (apply_subst_schm s sigma).
Proof.
  induction G; intros; crush.
Qed.

Hint Resolve in_ctx_stable_is_under_substitution.

Lemma not_in_ctx_stable_is_under_substitution : forall G s x,
    in_ctx x G = None -> in_ctx x (apply_subst_ctx s G) = None.
Proof.
  induction G; intros; crush.
Qed.

Hint Resolve not_in_ctx_stable_is_under_substitution.

Lemma is_constructor_schm_is_stable_under_substitution : forall sigma s,
    is_constructor_schm  sigma -> is_constructor_schm (apply_subst_schm s sigma).
Proof.
  induction sigma; intros; try econstructor; try inverts* H; eauto.
Qed.

Hint Resolve is_constructor_schm_is_stable_under_substitution.

Lemma is_schm_instance_is_stable_under_substitution : forall sigma tau s,
    is_schm_instance tau sigma ->  is_schm_instance (apply_subst s tau) (apply_subst_schm s sigma).
Proof.
  intros.
  unfold is_schm_instance in *.
  destruct H.
  eapply subst_inst_subst_type in H.
  exists (map_apply_subst_ty s x).
  apply H.
Qed.

Hint Resolve is_schm_instance_is_stable_under_substitution.

Lemma apply_inst_subst_nill : forall sigma,
      (exists tau, apply_inst_subst nil sigma = Some tau) \/
      apply_inst_subst nil sigma = None. 
Proof.
  induction sigma; intros.
  - left.
    exists (var i).
    eauto.
  - left.
    exists (con i).
    eauto.
  - right.
    simpl.
    crush.
  - destruct IHsigma1.
    destruct IHsigma2.
    left.
    destruct H, H0.
    exists (appl x x0).
    simpl. rewrite H.
    rewrite H0. reflexivity.
    right. simpl.
    destruct H. rewrite H.
    rewrite H0. reflexivity.
    right. destruct IHsigma2. destruct H0.
    simpl. rewrite H. reflexivity.
    simpl. rewrite H.
    reflexivity.
  - destruct IHsigma1.
    destruct IHsigma2.
    left.
    destruct H, H0.
    exists (arrow x x0).
    simpl. rewrite H.
    rewrite H0. reflexivity.
    right. simpl.
    destruct H. rewrite H.
    rewrite H0. reflexivity.
    right. destruct IHsigma2. destruct H0.
    simpl. rewrite H. reflexivity.
    simpl. rewrite H.
    reflexivity.
Qed.

Lemma is_schm_instance_arrow_proj2 : forall sigma2 sigma1 tau1 tau2,
    is_schm_instance (arrow tau1 tau2) (sc_arrow sigma1 sigma2) ->
    is_schm_instance tau2 sigma2. 
Proof.
  intros.
  inverts* H.
  exists x.
  simpl in *.
  destruct (apply_inst_subst x sigma1).
  - destruct (apply_inst_subst x sigma2).
    inverts* H0.
    inverts* H0.
  - inverts* H0.
Qed.
  
Hint Resolve is_schm_instance_arrow_proj2.

Lemma apply_subst_return_of_ty : forall sigma s tau,
    is_constructor_schm sigma ->
    is_schm_instance tau sigma ->
    apply_subst s (return_of_ty tau) = return_of_ty (apply_subst s tau). 
Proof.
  induction sigma; intros; try inverts* H.
  - apply is_schm_instance_must_be_con in H0.
    subst. reflexivity.
  - apply is_schm_instance_must_be_some_appl in H0.
    destruct H0 as [tau1' [tau2' H2]].
    subst.
    reflexivity.
  - apply is_schm_instance_must_be_some_arrow in H0 as H0'.
    destruct H0' as [tau1' [tau2' H0']].
    subst.
    assert (is_schm_instance tau2' sigma2). eauto.
    simpl.
    rewrite <- IHsigma2.
    reflexivity.
    auto.
    eauto.
Qed.    

(** has_pat is stable under substitution *)
Lemma has_type_pat_is_stable_under_substitution : forall p s tau G,
    has_type_pat G p tau -> has_type_pat (apply_subst_ctx s G) p (apply_subst s tau).
Proof.
  intros.
  apply (has_type_pat_mut
           (fun (G' : ctx) (p'': pat) tau => forall s tau',
                has_type_pat G' p'' tau' -> has_type_pat (apply_subst_ctx s G') p'' (apply_subst s tau'))
           (fun (G' : ctx) l (tau : ty) => forall s tau', 
                has_type_pats G' l tau' -> has_type_pats (apply_subst_ctx s G') l (apply_subst s tau'))
           ) with (p:=p) (t:=tau); intros; eauto.
  (** var case *)
  - econstructor; eauto.
  (** constr case *)
  - inverts* H1.
    + apply is_schm_instance_must_be_con in H2 as H2'.
      subst.
      inverts* H3. 
      inverts* H5. 
      erewrite apply_subst_return_of_ty; eauto.
      econstructor; eauto.
    + apply is_schm_instance_must_be_some_appl in H2 as H2'.
      destruct H2' as [tau1' [tau2' H2']].
      subst.
      inverts* H3.
      inverts* H5.
      erewrite apply_subst_return_of_ty; eauto.
      econstructor; eauto.
    + apply is_schm_instance_must_be_some_arrow in H2 as H2'.
      destruct H2' as [tau1' [tau2' H2']].
      subst.
      inverts* H3.
      inverts* H5.
      erewrite apply_subst_return_of_ty; eauto.
      econstructor; eauto.
  - inverts* H0.
    + econstructor.
    + econstructor.
  - inverts* H0.
    + econstructor.
    + econstructor.
  - inverts* H4.
    econstructor; eauto.
Qed.
     
Hint Resolve has_type_pat_is_stable_under_substitution.

(** has_pat is stable under substitution inversion *)

Lemma has_type_pats_is_stable_under_substitution : forall ps s tau G,
    has_type_pats G ps tau -> has_type_pats (apply_subst_ctx s G) ps (apply_subst s tau).
Admitted.

Hint Resolve has_type_pats_is_stable_under_substitution.

(** * Syntax-directed rule system of Damas-Milner *)

Inductive sub_ctx : ctx -> ctx -> Prop:=
| sub_ctx_cons : forall G1 G2, FV_ctx G1 = FV_ctx G2 ->
                                  (forall i' sigma', in_ctx i' G1 = Some sigma' ->
                                                in_ctx i' G2 = Some sigma') ->
                                  sub_ctx G1 G2.

Lemma no_free_variable_is_stable_under_substitution : forall s sigma,
    FV_schm sigma = nil -> FV_schm (apply_subst_schm s sigma) = nil.
Proof.
  induction sigma; intros; simpl in *; try reflexivity.
  - inverts* H.
  - apply app_eq_nil in H.
    destruct H.
    erewrite IHsigma1; eauto.
  - apply app_eq_nil in H.
    destruct H.
    erewrite IHsigma1; eauto.
Qed.

Hint Resolve no_free_variable_is_stable_under_substitution.

Lemma sub_ctx_is_stable_under_substitution : forall G2 G1 s,
    sub_ctx G1 G2 -> sub_ctx (apply_subst_ctx s G1) (apply_subst_ctx s G2).
Proof.
Admitted.

Hint Resolve sub_ctx_is_stable_under_substitution.

Inductive has_type : ctx -> term -> ty -> Prop :=
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
has_type_cases : ctx -> cases -> ty -> ty -> Prop :=
| one_term : forall G G' p e tau tau', sub_ctx G G' ->
                                  has_type_pat G p tau ->
                                  has_type G' e tau' -> 
                                  has_type_cases G (one_case p e) tau tau'
| many_terms : forall G p e tau tau' cs, has_type_cases G (one_case p e) tau tau' -> 
                                   has_type_cases G cs tau tau' ->
                                   has_type_cases G (many_cases p e cs) tau tau'.

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
           (fun  (G' : ctx) (l' : cases) (tau' tau'' : ty) => forall s tau1 tau2 G,
              has_type_cases G l' tau1 tau2 -> has_type_cases (apply_subst_ctx s G) l' (apply_subst s tau1) (apply_subst s tau2))
           ) with (c:=G) (t0:=tau); intros.
  (** var case *)
  - inversion H2.
    subst.
    econstructor; eauto.
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
  - inverts* H4.
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