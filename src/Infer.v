(** * The algorithm W
      This file contains the algorithm W, its proofs of soundness and completeness,
      and a bunch of auxiliary definitions.
    *)

Require Import LibTactics.
Require Import Unify.
Require Import Sublist.
Require Import Context.
Require Import ListIds.
Require Import Schemes.
Require Import SubstSchm.
Require Import Rename.
Require Import Disjoints.
Require Import Program.
Require Import Gen.
Require Import Omega.
Require Import Typing.
Require Import List.
Require Import NewTypeVariable.
Require Import HoareMonad.
Require Import Program.
Require Import MoreGeneral.
Require Import SimpleTypes.
Require Import Subst.
Require Import MyLtacs.
Require Import NonEmptyList.

(** * A bunch of auxiliary definitions *)

(** Monadic version of the function [apply_inst_subst]. *)
Program Definition apply_inst_subst_hoare (is_s : inst_subst) (sigma : schm):
  @Infer (@top id) ty (fun i r f => i = f /\ apply_inst_subst is_s sigma = Some r) :=
  match apply_inst_subst is_s sigma with
  | None => failT (SubstFailure' substFail) ty
  | Some tau => ret tau 
  end .

(** Gives a type that is a (new) instance of a scheme *)
Program Definition schm_inst_dep (sigma : schm) :
  @Infer (@top id) ty
         (fun i r f => f = i + (max_gen_vars sigma) /\
                    apply_inst_subst (compute_inst_subst i (max_gen_vars sigma)) sigma = Some r /\
                    (new_tv_schm sigma i -> new_tv_ty r f)) :=
  match max_gen_vars sigma as y with
  | nmax => 
    st <- get ;
      _ <- put (st + nmax) ;
      tau <- apply_inst_subst_hoare (compute_inst_subst st nmax) sigma ;
      ret tau
  end.
Next Obligation.
  simpl in *.
  destruct (apply_inst_subst_hoare (compute_inst_subst x (max_gen_vars sigma)) sigma >>= _).
  crush.
Defined.

(** Look up function used in algorithm W. *)
Program Definition look_dep (x : id) (G : ctx) :
  @Infer (@top id) schm (fun i k f => i = f /\ in_ctx x G = Some k) :=
  match in_ctx x G with
  | Some sig => ret sig
  | None => failT (@MissingVar' x (MissingVar x)) schm
  end.

(** Gives you a fresh variable *)
Program Definition fresh : @Infer (@top id) id (fun i x f => S i = f /\ i = x) :=
  fun n => exist _ (inleft (n, S n)) _.

(** Adds a fresh variable to the context *)
Program Definition addFreshCtx (G : ctx) (x : id) (alpha : id):
  @Infer (fun i => new_tv_ctx G i) ctx
         (fun i r f => alpha < i -> (new_tv_ctx r f /\ f = i /\ new_tv_ty (var alpha) f)) :=
  ret ((x, (sc_var alpha)) :: G).
Next Obligation.
  split; intros;
  unfold top; auto.
Defined.

Program Fixpoint check_has_no_vars (sigma : schm) {struct sigma} :
  @Infer (fun i => True) unit
         (fun i x f => i = f /\ no_vars sigma) := 
  match sigma with
  | sc_gen _ => ret tt
  | sc_con _ => ret tt
  | sc_appl sigma1 sigma2 =>
       u <- check_has_no_vars sigma1 ;
       u' <- check_has_no_vars sigma2 ;
       ret u'
  | sc_arrow sigma1 sigma2 =>
       u <- check_has_no_vars sigma1 ;
       u' <- check_has_no_vars sigma2 ;
       ret u'
  | sc_var i => failT (@HasVarFailure' (sc_var i) (HasVar (sc_var i))) unit
  end.
Next Obligation.
  splits; eauto; econstructor.
Defined.
Next Obligation.
  splits; eauto; econstructor.
Defined.
Next Obligation.
  intros.
  edestruct (check_has_no_vars sigma1 >>= _); crush.
  econstructor; eauto.
Defined.
Next Obligation.
  intros.
  edestruct (check_has_no_vars sigma1 >>= _); crush.
  econstructor; eauto.
Defined.
  

Program Fixpoint check_is_constructor (sigma : schm) {struct sigma} :
  @Infer (fun i => True) unit
         (fun i x f => i = f /\ is_constructor_schm sigma) :=
  match sigma with
  | sc_con _ => ret tt
  | sc_appl sigma1 sigma2 => 
      u <- @check_has_no_vars sigma1 ;
      u' <- @check_has_no_vars sigma2 ;
      ret u'
  | sc_arrow sigma1 sigma2 =>
      u <- @check_has_no_vars sigma1 ;
      u' <- @check_is_constructor sigma2 ;
      ret u'
  | sc_var i => failT (@NotConstructorFailure' (sc_var i) (NotConstructor (sc_var i))) unit
  | sc_gen i => failT (@NotConstructorFailure' (sc_gen i) (NotConstructor (sc_gen i))) unit
  end.
Next Obligation.
  splits; eauto.
  econstructor.
Defined.
Next Obligation.
  destruct (check_has_no_vars sigma1 >>= _); crush.
  econstructor; eauto.
Defined.
Next Obligation.
  destruct (check_has_no_vars sigma1 >>= _); crush.
  econstructor; eauto.
Defined.

(** * Completeness for pattern *)

Definition completeness_pat (p : pat) (J : ctx) (tau : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution),
    has_type_pat (apply_subst_ctx phi J) p tau' -> 
    exists s', tau' = apply_subst s' tau /\
          (forall x : id, x < st -> apply_subst phi (var x) = apply_subst s' (apply_subst s (var x))).

Definition completeness_pats (x : id) (ps : pats) (J : ctx) (tau : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution),
    has_type_pats x (apply_subst_ctx phi J) ps tau' -> 
    exists s', tau' = apply_subst s' tau /\
          (forall x : id, x < st -> apply_subst phi (var x) = apply_subst s' (apply_subst s (var x))).

Lemma is_constructor_schm_return_of_ty : forall tau sigma, is_constructor_schm sigma ->
                                                      is_schm_instance tau sigma ->
                                                      exists s, return_of_ty tau = return_of_ty (apply_subst s tau).
Proof.
  induction tau; intros.
  - exists (nil:substitution). reflexivity.
  - exists (nil:substitution). reflexivity.
  - exists (nil:substitution). crush.
  - inverts* H.
    + inverts* H0.
      simpl in H. inverts H.
    + inverts* H0.
      simpl in H.
      cases (apply_inst_subst x sigma1).
      cases (apply_inst_subst x sigma2).
      inverts* H.
      inverts* H.
      inverts* H.
    + edestruct IHtau2 with (sigma:=sigma2); auto.
      eauto.
      exists x.
      simpl.
      auto.
Qed.      

(**
Lemma completeness_pat_returno_of_ty : forall tau s i x ps J sigma,
    is_constructor_schm sigma -> is_schm_instance tau sigma ->
    completeness_pat (constr_p x ps) J tau s i -> completeness_pat (constr_p x ps) J (return_of_ty tau) s i.
Proof.
  intros. intro. intros.
  edestruct H1 as [s' [P1 P2]].
  { eauto. }
  edestruct is_constructor_schm_return_of_ty as [s'' ]; eauto.
  exists s''.
  split.
  - Abort.      
*)

(** * The pattern inference *)

Program Fixpoint inferPat (p : pat) (J : ctx) {struct p} :
  @Infer (fun i => new_tv_ctx J i /\ is_constructor_ctx J) (ty * ctx * substitution)
         (fun i x f => i <= f /\ new_tv_ctx (snd (fst x)) f /\
                    new_tv_ty (fst (fst x)) f /\ new_tv_subst (snd x) f /\
                    has_type_pat J p (fst (fst x)) /\
                    completeness_pat p J (fst (fst x)) (snd x) i) :=
  match p with
  | var_p x =>
      alpha <- fresh ;
      ret (var alpha, (x, sc_var alpha)::nil, nil)

  | constr_p x ps =>
      sigma <- look_dep x J ;
      _ <- check_is_constructor sigma ;
      tau <- schm_inst_dep sigma ;
      s_G <- inferPats x sigma ps tau J ;
      ret (apply_subst (fst s_G) (return_of_ty tau), apply_subst_ctx (fst s_G) (snd s_G), fst s_G)
  end
with inferPats (x0 : id) (sigma : schm) (pss : pats) (tau: ty) (J : ctx) {struct pss} : 
       @Infer (fun i => new_tv_ctx J i /\ new_tv_ty tau i /\ is_constructor_ctx J /\ in_ctx x0 J = Some sigma /\
                     apply_inst_subst (compute_inst_subst (i - (max_gen_vars sigma)) (max_gen_vars sigma)) sigma = Some tau)
           (substitution * ctx)
         (fun i x f => i <= f /\ new_tv_ctx (snd x) f /\ new_tv_subst (fst x) f /\
                    has_type_pats x0 J pss (apply_subst (fst x) tau) /\
                    completeness_pats x0 pss J (apply_subst (fst x) tau) (fst x) (i - (max_gen_vars sigma))) :=
       match pss, tau with
       | no_pats, (con i) => ret (nil, nil)
       | no_pats, (appl tau1 tau2) => ret (nil, nil)
       | (some_pats p ps'), (arrow tau1 tau2) =>
           tau_G_s <- inferPat p J ; 
           s <- unify (apply_subst (snd tau_G_s) tau1) (fst (fst tau_G_s)) ;
           s_G <- inferPats x0 sigma ps' (apply_subst s (apply_subst (snd tau_G_s) tau2)) J ;
           ret (compose_subst (snd tau_G_s) (compose_subst s (fst s_G)), snd (fst tau_G_s))
       | no_pats, (arrow tau1 tau2) => failT (@PatsFailure' (arrow tau1 tau2) no_pats (MissingPatArrow tau1 tau2)) (substitution * ctx)
       | no_pats, (var i) => failT (@PatsFailure' (var i) no_pats (MissingPatVar i)) (substitution * ctx)
       | (some_pats p ps), (var i) => failT (@PatsFailure' (var i) (some_pats p ps) (HasPatVar i p ps)) (substitution * ctx)
       | (some_pats p ps), (con i) => failT (@PatsFailure' (con i) (some_pats p ps) (HasPatCon i p ps)) (substitution * ctx)
       | (some_pats p ps), (appl tau1 tau2) => failT (@PatsFailure' (appl tau1 tau2) (some_pats p ps) (HasPatAppl tau1 tau2 p ps)) (substitution * ctx)
       end.
Next Obligation. 
  unfold top;
    splits; intros;
      try splits; auto.
Defined.
Next Obligation. (* var_p case *)
  splits; auto.
  econstructor.
  intro. intros.
  exists ((x0, tau')::phi).
  split.
  - crush.
  - intros.
    simpl.
    destruct (eq_id_dec x0 x1); try omega.
    reflexivity.
Defined.
Next Obligation. 
  unfold top;
    splits; intros;
      try splits; auto;
        intros; auto; splits; eauto.
  destructs H0.
  intros; splits; auto.
  destructs H2.
  subst.
  splits; eauto.
  destruct H. subst. eauto.
  destruct H. subst. eauto.
  destructs* H.
  destructs* H.
  subst.
  assert ((s0 + max_gen_vars x1 - max_gen_vars x1) = s0).
  { omega. }
  rewrite H.
  auto.
Defined.
Next Obligation.
  destruct (look_dep x J >>= _); crush; clear inferPats; sort;
  rename x2 into tau;
  rename x3 into alpha;
  rename x1 into sigma;
  rename x4 into s;
  rename t2 into J'.
  - eapply new_tv_apply_subst_ty. 
    apply new_tv_ty_return_of_ty.
    eapply new_tv_ty_trans_le; eauto.
    auto.
  - destruct sigma.
    (** sc_var *)
    + inverts* H2.
    (** sc_con *)
    + simpl in H.
      inverts* H.
      inverts* H7.
      rewrite H5 in H1.
      inverts* H1.
      erewrite apply_subst_return_of_ty; eauto.
      econstructor; eauto.
      exists (nil:inst_subst). reflexivity.
      econstructor; eauto.
      exists (nil:inst_subst). reflexivity.
    (** gen *)
    + inverts* H2.
    (** sc_appl *)
    + simpl in H.
      cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      {
        cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
        { inversion H.
          rename t0 into tau1, t1 into tau2.
          rewrite <- H9 in H7.
          inversion H7.
          subst.
          rewrite H11 in H1.
          inverts* H1.
          simpl.
          assert (appl (apply_subst s tau1) (apply_subst s tau2) = return_of_ty (appl (apply_subst s tau1 ) (apply_subst s tau2))).
          { reflexivity. }
          rewrite H1.
          econstructor.
          assert (in_ctx x J = in_ctx x (apply_subst_ctx s J)).
          { rewrite apply_subst_ctx_is_constructor; eauto. }
          rewrite H5.
          info_eauto.
          eauto.
          destruct H16.
          eauto.
          exists (map_apply_subst_ty s ((compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))))).
          rewrite <- apply_subst_appl.
          apply subst_inst_subst_type.
          simpl.
          rewrite Eq, Eq0.
          reflexivity.
          auto.
        }
        inverts* H. }
        inverts* H.
    (** sc_arrow *)
    + simpl in H.
      cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inversion H.
      rename t0 into tau1, t1 into tau2.
      erewrite apply_subst_return_of_ty; eauto.
      econstructor.
      eapply apply_subst_ctx_is_constructor in i. 
      rewrite <- i. eauto.
      eauto.
      exists (map_apply_subst_ty s (compute_inst_subst alpha (max_gen_vars (sc_arrow sigma1 sigma2)))).
      simpl.
      eapply subst_inst_subst_type in Eq.
      eapply subst_inst_subst_type in Eq0.
      rewrite Eq, Eq0.
      reflexivity.
      rewrite <- H9 in H7.
      eauto.
      exists ((compute_inst_subst alpha (max_gen_vars (sc_arrow sigma1 sigma2)))).
      simpl.
      rewrite Eq, Eq0.
      reflexivity.
      inverts H.
      inverts H.
   - (* Case: constr_t completeness *)
     intro. intros.
     unfold completeness_pats in *.
     rename H8 into COMPL_ps, H7 into SOUND_ps.
     inverts H5.
     inverts H12.
     erewrite apply_subst_ctx_is_constructor in H9; eauto.
     rewrite H9 in H1.
     inverts H1.
     rename x1 into is_s.
          edestruct is_constructor_schm_return_of_ty as [ss Hj].
     { apply H10. }
     { exists (is_s).
       apply H5. }
     edestruct COMPL_ps as [s' [PRINC_ps1 PRINC_ps2]].
     { eapply stronger_has_type_pats_is_stable_under_substitution in H14. apply H14. }
     exists s'.
     splits.
     {
       - erewrite apply_subst_return_of_ty; auto.
         + erewrite apply_subst_return_of_ty; auto.
           * rewrite PRINC_ps1 in Hj.
             rewrite Hj.
             reflexivity.
           * erewrite <- apply_subst_schm_is_constructor in H10.
             apply H10.
             apply H10.
           * exists (map_apply_subst_ty s (compute_inst_subst alpha (max_gen_vars sigma))).
             apply subst_inst_subst_type; auto.
         + eauto.
         + exists (compute_inst_subst alpha (max_gen_vars sigma)).
           eauto.
        }
     { intros.
       apply PRINC_ps2.
       omega.
     }
Defined.      
Next Obligation.
  unfold top; auto.
Defined.      
Next Obligation.
  splits; eauto.
  - try econstructor.
    eauto.
    eauto.
    exists (compute_inst_subst (x - max_gen_vars sigma) (max_gen_vars sigma)).
    eauto.
    reflexivity.
  -
  intro. intros.
  (** completeness_pats con case *)
  inversion_clear H.
  (** con case *)
  + rewrite apply_subst_ctx_is_constructor in H0; eauto.
    assert (is_constructor_schm sigma).
    { eauto. }
    assert (is_constructor_schm sigma0).
    { eauto. }
    rewrite H0 in e.
    inversion e.
    destruct sigma.
    * subst. inverts* H4.
    * inverts* e.
      apply is_schm_instance_must_be_con in H2.
      subst.
      inverts* H3.
      simpl in e0.
      inverts* e0.
    * subst. inverts* H4.
    * subst. inverts* e0.
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inverts* H6.
      inverts* H6.
      inverts* H6.
    * subst. inverts* e0.
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inverts* H6.
      inverts* H6.
      inverts* H6.
  + rewrite apply_subst_ctx_is_constructor in H0; eauto.
    assert (is_constructor_schm sigma).
    { eauto. }
    assert (is_constructor_schm sigma0).
    { eauto. }
    rewrite H0 in e.
    inversion e.
    destruct sigma.
    * subst. inverts* H4.
    * inverts* e.
      apply is_schm_instance_must_be_con in H2.
      subst.
      inverts* H3.
    * subst. inverts* H4.
    * subst. inverts* e0.
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inverts* H6.
      inverts* H6.
      inverts* H6.
    * subst. inverts* e0.
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inverts* H6.
      inverts* H6.
      inverts* H6.
Defined.      
Next Obligation.
  unfold top; auto.
Defined.      
Next Obligation.
  splits; eauto.
  (** soundness_pats appl case *)
  - try econstructor.
    eauto.
    eauto.
    exists (compute_inst_subst (x - max_gen_vars sigma) (max_gen_vars sigma)).
    eauto.
    fold (apply_subst nil tau1).
    fold (apply_subst nil tau2).
    crush.
  (** completeness_pats appl case *)
  - intro. intros.
  inversion_clear H.
  (** con case *)
  + rewrite apply_subst_ctx_is_constructor in H0; eauto.
    assert (is_constructor_schm sigma).
    { eauto. }
    assert (is_constructor_schm sigma0).
    { eauto. }
    rewrite H0 in e.
    inversion e.
    destruct sigma.
    * subst. inverts* H4.
    * inverts* e0.
    * subst. inverts* H4.
    * subst.
      apply is_schm_instance_must_be_some_appl in H2.
      destruct H2 as [tau1' [tau2' H2]].
      subst.
      inverts* H3.
    * subst.
      inverts* e0.
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inverts* H6.
      inverts* H6.
      inverts* H6.
  + rewrite apply_subst_ctx_is_constructor in H0; eauto.
    assert (is_constructor_schm sigma).
    { eauto. }
    assert (is_constructor_schm sigma0).
    { eauto. }
    rewrite H0 in e.
    inversion e.
    subst.
    assert (exists sigma1 sigma2, sigma = sc_appl sigma1 sigma2).
    { destruct sigma ; try inverts* H4.
      inverts* e0.
      inverts* e0.
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      destruct (apply_inst_subst (compute_inst_subst (x - Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2)) (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inverts* H5.
      inverts* H5.
      inverts* H5. }
    destruct H5 as [sigma1 [sigma2 H5]].
    subst.
    apply is_schm_instance_must_be_some_appl in H2 as H2'.
    destruct H2' as [tau1' [tau2' H2']].
    subst.
    inverts* H3.
    destruct H2.
    exists (compute_subst (x - max_gen_vars (sc_appl sigma1 sigma2)) x1 ++ phi).
    split; repeat rewrite apply_subst_nil.
    * eapply new_tv_schm_compute_inst_subst with (p := max_gen_vars (sc_appl sigma1 sigma2)). 
      { eapply new_tv_ctx_implies_new_tv_schm. 
        apply H0.
        skip. (** aqui *)
        }
      { reflexivity. }
      { auto. }
      { rewrite apply_subst_schm_is_constructor; eauto. }
    * intros.
      rewrite apply_subst_nil.
      rewrite find_subst_some_apply_app_compute_subst.
      reflexivity.
      auto.
Defined.      
Next Obligation.
  (** aqui 2 *)
  unfold top; intros;
    splits; intros;
      try splits; auto;
        intros; eauto. 
  destructs H0.
  destructs H.
  splits; intros; eauto.
  subst.
  destruct x0.
  simpl in *.
  splits; eauto.
  eapply new_tv_apply_subst_ty; eauto.
  eapply new_tv_apply_subst_ty; eauto.
  inverts* n0.
  inverts* n0.
  Unshelve. auto.
  Unshelve. auto.
Defined.
Next Obligation.
  destruct (inferPat p J >>= _); crush.
  rename x1 into s1, x2 into s2;
  rename t3 into G', t1 into s;
  rename x0 into tau.
  - eapply new_tv_compose_subst; eauto. 
    eapply new_tv_compose_subst; eauto. 
    eapply new_tv_subst_trans; eauto.
    apply H7; crush.
    eapply new_tv_apply_subst_ty; eauto.
    inverts* n0.
  - econstructor.
    + inverts* n0.
      repeat erewrite apply_compose_equiv. 
      crush.
    + repeat erewrite apply_compose_equiv. 
      auto.
      Unshelve. auto.
      Unshelve. auto.
Defined.
Next Obligation.
  unfold top; auto.
Defined.
Next Obligation.
  unfold top; auto.
Defined.
Next Obligation.
  unfold top; auto.
Defined.
Next Obligation.
  unfold top; auto.
Defined.
Next Obligation.
  unfold top; auto.
Defined.

(** * Completeness theorem definition. *)

Definition completeness (e : term) (G J : ctx) (tau : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution),
    has_type (apply_subst_ctx phi G) J e tau' -> 
    exists s', tau' = apply_subst s' tau /\
          (forall x : id, x < st -> apply_subst phi (var x) = apply_subst s' (apply_subst s (var x))).

Definition completeness_cases (cs : cases) (G J : ctx) (tau1 tau2 : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution),
    has_type_cases (apply_subst_ctx phi G) J cs (apply_subst phi tau1) tau' ->
    exists s', tau' = apply_subst s' tau2 /\
          (forall x : id, x < st -> apply_subst phi (var x) = apply_subst s' (apply_subst s (var x))).

(** * The algorithm W itself *)

Program Fixpoint W (e : term) (G J: ctx) {struct e} :
  @Infer (fun i => new_tv_ctx G i /\ new_tv_ctx J i /\ is_constructor_ctx J) (ty * substitution)
         (fun i x f => i <= f /\ new_tv_subst (snd x) f /\ new_tv_ty (fst x) f /\
                    new_tv_ctx (apply_subst_ctx (snd x) G) f /\
                    new_tv_ctx (apply_subst_ctx (snd x) J) f /\
                    has_type (apply_subst_ctx ((snd x)) G) J e (fst x) /\
                    completeness e G J (fst x) ((snd x)) i) :=
  match e with
  | constr_t x =>
      sigma <- look_dep x J ;
      _ <- check_is_constructor sigma ;
      tau <- schm_inst_dep sigma ;
      ret (tau, nil)
  | var_t x =>
      sigma <- look_dep x G ;
      tau <- schm_inst_dep sigma ;
      ret (tau, nil)

  | lam_t x e' =>
      alpha <- fresh ;
      G' <- addFreshCtx G x alpha ;
      tau_s <- W e' G' J ;
      ret ((arrow (apply_subst ((snd tau_s)) (var alpha)) (fst tau_s)), (snd tau_s))

  | app_t l r =>
      tau1_s1 <- W l G J ;
      tau2_s2 <- W r (apply_subst_ctx (snd tau1_s1) G) J ;
      alpha <- fresh ;
      s <- unify (apply_subst (snd tau2_s2) (fst tau1_s1)) (arrow (fst tau2_s2) (var alpha)) ;
      ret (apply_subst s (var alpha), compose_subst  (snd tau1_s1) (compose_subst (snd tau2_s2) s))

  | let_t x e1 e2  =>
      tau1_s1 <- W e1 G J ;
      tau2_s2 <- W e2 ((x,gen_ty (fst tau1_s1)
                      (apply_subst_ctx (snd tau1_s1) G) )::(apply_subst_ctx (snd tau1_s1) G)) J ;
      ret (fst tau2_s2, compose_subst (snd tau1_s1) (snd tau2_s2))

  | case_t e' cs =>
      tau1_s1 <- W e' G J ;
      tau2_s2 <- infer_cases cs (fst tau1_s1) (apply_subst_ctx (snd tau1_s1) G) J;
      ret (fst tau2_s2, compose_subst (snd tau1_s1) (snd tau2_s2)) 
  end
with infer_cases (cs : cases) (tau : ty) (G J : ctx) {struct cs} :
       @Infer (fun i => new_tv_ctx G i /\ new_tv_ctx J i /\ new_tv_ty tau i /\ is_constructor_ctx J) (ty * substitution)
              (fun i x f => i <= f /\ new_tv_ty (fst x) f /\ new_tv_subst (snd x) f /\
                         has_type_cases (apply_subst_ctx (snd x) G) J cs (apply_subst (snd x) tau) (fst x) /\
                         completeness_cases cs G J tau (fst x) (snd x) i) :=
       match cs with
       | one_case p e =>
          tau_G_s <- inferPat p J ;
          s <- unify (apply_subst (snd tau_G_s) tau) (fst (fst tau_G_s)) ;
          tau_s <- W e (apply_subst_ctx s (apply_subst_ctx (snd tau_G_s) ((snd (fst tau_G_s) ++ G)))) J ;
          ret (fst tau_s, compose_subst (snd tau_G_s) (compose_subst s (snd tau_s)))
       | many_cases p e cs' =>
          tau_G_s <- inferPat p J ;
          s <- unify (apply_subst (snd tau_G_s) tau) (fst (fst tau_G_s)) ;
          tau_s <- W e (apply_subst_ctx s (apply_subst_ctx (snd tau_G_s) ((snd (fst tau_G_s) ++ G)))) J;

          tau_s' <- infer_cases cs' (apply_subst (compose_subst (snd tau_G_s) (compose_subst s (snd tau_s))) tau)
                   (apply_subst_ctx (compose_subst (snd tau_G_s) (compose_subst s (snd tau_s))) G) J ;
          s' <- unify (apply_subst (snd tau_s') (fst tau_s)) (fst tau_s') ;
          ret (apply_subst s' (fst tau_s'), (compose_subst (snd tau_G_s) (compose_subst s (compose_subst (snd tau_s) ((compose_subst (snd tau_s') s'))))))
       end.
Next Obligation.
  intros; unfold top; auto.
Defined.
Next Obligation.  (* Case: postcondition of constr *)
  edestruct (look_dep x J >>= _); crush;
    rename x into st0, x2 into st1;
    rename x0 into tau', x1 into sigma'.
  - (* Case: constr_t soundness *)
    econstructor; eauto. 
    unfold is_schm_instance. exists (compute_inst_subst x3 (max_gen_vars sigma')).
    eauto.
  (* Case: constr_t completeness *)
  - subst.
    unfold completeness.
    intros.
    inverts* H3.
    inverts* H9.
    rewrite H5 in H1.
    inverts* H1.
    rename x into is_s.
    exists ((compute_subst x3 is_s) ++ phi).
    splits.
    + eapply new_tv_schm_compute_inst_subst with (p := max_gen_vars sigma'). 
      * eapply new_tv_ctx_implies_new_tv_schm; 
          crush.
      * reflexivity.
      * auto.
      * sort.
        crush.
    + intros.
      rewrite apply_subst_nil.
      rewrite find_subst_some_apply_app_compute_subst.
      reflexivity.
      assumption. 
Defined.
Next Obligation.
  intros; unfold top; auto.
Defined.
Next Obligation.  (* Case: postcondition of var *)
  edestruct (look_dep x G >>= _);
    crush; 
    rename x into st0, x2 into st1;
    rename x0 into tau', x1 into tau.
  - (* Case: var_t soundness *)
    econstructor; eauto. 
    unfold is_schm_instance. exists (compute_inst_subst st1 (max_gen_vars tau)).
    rewrite apply_subst_schm_nil. auto.
  (* Case: var_t completeness *)
  - subst.
    unfold completeness.
    intros.
    inversion H2.
    subst.
    inversion H7.
    rename x into is_s.
    destruct (@assoc_subst_exists G st0 phi sigma H4) as [sigma' H4'].
    destruct H4' as [H41  H42].
    destruct H7.
    exists ((compute_subst st1 is_s) ++ phi).
    splits.
    + eapply new_tv_schm_compute_inst_subst with (p := max_gen_vars sigma'). 
      * eapply new_tv_ctx_implies_new_tv_schm; 
          crush.
      * reflexivity.
      * rewrite H1 in H41.
        inverts* H41.
      * sort.
        rewrite H1 in H41.
        inverts* H41.
        crush.
    + intros.
      rewrite apply_subst_nil.
      rewrite find_subst_some_apply_app_compute_subst.
      reflexivity.
      assumption. 
Defined.
Next Obligation. 
  splits; intros; unfold top; auto;
    crush. intros. crush. 
  destructs H; eauto.
  splits; crush.
Defined.
Next Obligation. (* Case: postcondition of lambda  *)
  simpl.
  destruct (W e' (((x, sc_var x0)) :: G) J >>= _);
    crush; clear W;
      rename x0 into st0, t1 into s, x1 into tau_r, t into st1.
  (* Subcase : new_tv_ty lambda *)
  - destruct (find_subst s st0).
    + rename t into tau_l.
      econstructor; eauto.
      inversion H3.
      subst.
      eapply new_tv_ty_to_schm; eauto.
    + econstructor; eauto.
  (* Subcase : soundness lambda *)
  - econstructor.
    simpl in H0.
    assert (sc_var st0 = ty_to_schm (var st0)). auto.
    cases (find_subst s st0);
      simpl;
      auto.
  (* Subcase : completeness lambda *)
  - unfold completeness. 
    intros.
    inversion_clear H1.
    fold (apply_subst s (var st0)).
    cut (exists s' : substitution,
            tau'0 = apply_subst s' tau_r /\
            (forall x' : id, x' < S st0 ->  apply_subst (((st0, tau):: phi)) (var x') =
                                      apply_subst s' (apply_subst s (var x'))) ) .
    intros.
    destruct H1; auto.
    destruct H1; auto.
    rename x0 into s'.
    exists s'.
    split.
    * rewrite apply_subst_arrow.
      rewrite H1 at 1.
      specialize H8 with (x' := st0).
      simpl in *.
      destruct (eq_id_dec st0 st0); intuition.
      destruct (find_subst s st0);
        fequals; eauto.
    * intros;
        rewrite <- H8; eauto.
      erewrite add_subst_rewrite_for_unmodified_id; auto; try omega.
    * unfold completeness in H6.
      specialize H6 with (phi := (st0, tau)::phi).
      edestruct H6.
      assert (sc_var st0 = ty_to_schm (var st0)); eauto.
      erewrite <- add_subst_add_ctx in H7. 
      eauto.
      eauto.
      exists x0.
      assumption.
Defined.
Next Obligation. 
  unfold top.
  intros; splits; auto.
  intros; splits; auto.
  destructs H;
    try splits; auto.
  eauto.
  Unshelve. auto.
  Unshelve. auto.
Defined.
Next Obligation. (* Case: postcondition of application  *)
  destruct (W l G J >>= _);
  crush;
    clear W;
    rename H7 into MGU, H14 into MGU', H16 into MGU'';
    rename x4 into alpha, x into st0, x1 into st1;
    rename x3 into mu, t1 into s1, t2 into s2;
    rename H6 into COMP_L, H13 into COMP_R;
    rename x2 into tauL, x0 into tauLR.
  (* Subcase : new_tv_subst application *)
  - apply new_tv_compose_subst; eauto.
    apply new_tv_compose_subst; eauto.
    eapply MGU'.
    splits; eauto.
    econstructor; eauto.
  (* Subcase : new_tv_ty application *)
  - fold (apply_subst mu (var alpha)).
    subst.
    apply new_tv_apply_subst_ty; eauto.
    apply MGU'; eauto.
    splits; eauto.
    econstructor; eauto.
  (* Subcase : new_tv_ctx G application *)
  - subst.
    eapply new_tv_s_ctx; eauto.
    apply new_tv_compose_subst; eauto.
    apply new_tv_compose_subst; eauto.
    eapply MGU'.
    splits; eauto.
    econstructor; eauto.
  (* Subcase : new_tv_ctx J application *)
  - subst.
    eapply new_tv_s_ctx; eauto.
    apply new_tv_compose_subst; eauto.
    apply new_tv_compose_subst; eauto.
    eapply MGU'.
    splits; eauto.
    econstructor; eauto.
  (* Subcase : soundness application *)
  - fold (apply_subst mu (var alpha)) in *.
    subst.
    repeat rewrite apply_subst_ctx_compose.
    apply app_ht with (tau := apply_subst mu tauL); eauto.
    rewrite <- MGU'';
      eauto.
  (* Subcase : completeness application *)
  - subst.
    unfold completeness. intros.
    rename H6 into SOUND_LR.
    inversion_clear SOUND_LR.
    rename tau into tau_l.
    rename tau' into tau_r.
    rename H6 into SOUND_L, H7 into SOUND_R.
    sort.
    apply COMP_L in SOUND_L as PRINC_L.
    destruct PRINC_L as [psi1 PRINC_L].
    destruct PRINC_L as [PRINC_L1 PRINC_L2].
    cut (exists psi2, (tau_l = apply_subst psi2 tauL /\
         forall x0 : id, x0 < st1 -> apply_subst psi1 (var x0) = apply_subst psi2 (apply_subst s2 (var x0)))).
    intros PRINC_R.
    destruct PRINC_R as [psi2 [PRINC_R1 PRINC_R2]].
    specialize MGU with (s':= ((alpha, tau_r)::psi2)).
    destruct MGU as [s_psi MGU].
    {
      fold (apply_subst ((alpha, tau_r)::psi2) (var alpha)).
      simpl. destruct (eq_id_dec alpha alpha); intuition.
      erewrite (@add_subst_new_tv_ty psi2 alpha tauL); eauto.
      rewrite <- PRINC_R1.
      erewrite <- (@new_tv_compose_subst_type psi1 s2 ((alpha, tau_r)::psi2) st1 tauLR); eauto.
      intros.
      erewrite add_subst_new_tv_ty; eauto. 
    }
    fold (apply_subst mu (var alpha)).
    exists s_psi.
    splits.
    + rewrite <- apply_compose_equiv.
      rewrite <- MGU.
      mysimp.
    + intros.
      repeat rewrite apply_compose_equiv.
      repeat rewrite <- apply_compose_equiv.
      rewrite apply_compose_equiv.
      rewrite apply_compose_equiv.
      rewrite <- MGU.
      rewrite add_subst_new_tv_ty.
      erewrite <- (new_tv_compose_subst_type psi1 s2 psi2); eauto.
      apply new_tv_apply_subst_ty; auto.
      eapply new_tv_ty_trans_le; eauto. 
    + eapply COMP_R; eauto.
      erewrite <- new_tv_compose_subst_ctx;
      eauto.
Defined.
Next Obligation.
  unfold top.
  intros; splits; eauto.
  intros; splits; eauto.
  destructs H;
    try splits; eauto.
  Unshelve. auto.
  Unshelve. auto.
Defined.
Next Obligation. (* Case : postcondition of let *)
  destruct (W e1 G J >>= _).
  crush;
    clear W;
    rename H12 into SOUND_e2, H5 into SOUND_e1;
    rename H6 into COMP_e1, H13 into COMP_e2;
    rename x into st0, t into st3;
    rename x3 into tau_e2, t2 into s2, x2 into st2;
    rename x1 into tau_e1, t1 into s1, x0 into st1;
    eauto.
  (* Subcase : new_tv_ctx G let *)
  - eapply new_tv_s_ctx; eauto. 
  (* Subcase : new_tv_ctx J let *)
  - eapply new_tv_s_ctx; eauto. 
  (* Subcase : soundness let *)
  - pose proof exists_renaming_not_concerned_with (gen_ty_vars tau_e1 (apply_subst_ctx s1 G))
         (FV_ctx (apply_subst_ctx s1 G)) (FV_subst s2)  as renaming.
    destruct renaming as [rho renaming].
    inversion renaming.
    subst.
    pose proof (gen_ty_in_subst_ctx
                  (apply_subst_ctx s1 G) s2 (apply_subst (rename_to_subst rho) tau_e1)) as hip.
    pose proof (renaming_not_concerned_with_gen_vars) as hip2.
    apply hip2 in renaming as renaming'.
    apply hip in renaming' as renaming''.
    pose proof (subst_ctx_when_s_disjoint_with_ctx
                  (apply_subst_ctx s1 G) (rename_to_subst rho)) as disj_ctx_subst. 
    pose proof (apply_subst_ctx_compose G (rename_to_subst rho) s1) as rename_compose.
    pose proof (subst_ctx_when_s_disjoint_with_ctx
                  (apply_subst_ctx s1 J) (rename_to_subst rho)) as disj_ctx_subst'. 
    pose proof (apply_subst_ctx_compose J (rename_to_subst rho) s1) as rename_compose'.
    apply let_ht with (tau:= apply_subst s2 (apply_subst (rename_to_subst rho) tau_e1)).
    repeat rewrite apply_subst_ctx_compose.
    repeat rewrite apply_subst_ctx_compose.
    eapply has_type_is_stable_under_substitution.
    erewrite <- disj_ctx_subst.
    eauto.
    rewrite dom_rename_to_subst.
    rewrite H6.
    apply free_and_bound_are_disjoints; eauto.
    rewrite apply_subst_ctx_compose; eauto.
    rewrite <- gen_ty_in_subst_ctx; eauto.
    rewrite <- subst_add_type_scheme; eauto.
    rewrite <- gen_apply_rename_to_subst; eauto.
  (* Subcase : completeness let *)
  - intro. intros.
    rename H5 into SOUND_let.
    inversion_clear SOUND_let.
    rename H5 into SOUND2_e1.
    rename H6 into SOUND2_e2.
    rename tau into tau_e1', tau' into tau_e2'.
    sort.
    apply COMP_e1 in SOUND2_e1 as PRINC_e1.
    destruct PRINC_e1 as [psi1 [PRINC_e11 PRINC_e12]].
    cut (exists psi2, (tau_e2' = apply_subst psi2 tau_e2 /\
         forall x0 : id, x0 < st2 -> apply_subst psi1 (var x0) = apply_subst psi2 (apply_subst s2 (var x0)))).
    intro PRINC_e2.
    destruct PRINC_e2 as [psi2 [PRINC_e21 PRINC_e22]].
    exists psi2.
    split; auto.
    intros.
    rewrite apply_compose_equiv.
    erewrite <- (new_tv_compose_subst_type psi1 s2 psi2); eauto.
    eapply COMP_e2.
    rewrite subst_add_type_scheme.
    eapply typing_in_a_more_general_ctx with
        (G2 := (st0, (gen_ty (apply_subst psi1 tau_e1)
               (apply_subst_ctx psi1 (apply_subst_ctx s1 G))))::(apply_subst_ctx psi1 (apply_subst_ctx s1 G))). 
    eapply more_general_ctx_cons. eauto.
    eapply more_general_gen_ty_before_apply_subst.
    rewrite <- PRINC_e11.
    erewrite <- new_tv_compose_subst_ctx; eauto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
Defined.
Next Obligation.
  unfold top.
  intros; splits; eauto.
  intros; splits; eauto.
  destructs H;
    try split; eauto.
Defined.
Next Obligation.
  destruct (W e' G J >>= _); crush;
    rename x2 into tau, x0 into tau';
    rename x into i0, x1 into i1, t into i2;
    rename t2 into s2, t1 into s1.
  - repeat rewrite apply_subst_ctx_compose;
    eauto.
  - repeat rewrite apply_subst_ctx_compose;
    eauto.
  - econstructor.
    repeat rewrite apply_subst_ctx_compose.
    eauto.
    repeat rewrite apply_subst_ctx_compose.
    eauto.
  - intro. intros.
    rename H8 into SOUND_case.
    rename H6 into COMPL_e', H5 into SOUND_e'.
    rename H11 into COMPL_cs, H10 into SOUND_cs.
    inverts SOUND_case.
    rename H11 into SOUND_e'2, H13 into SOUND_cs_2.
    unfold completeness_cases in COMPL_cs.
    edestruct COMPL_e' as [s'' [PRINC_e1 PRINC_e2]].
    {eauto. }
    edestruct COMPL_cs as [s' [PRINC_cs1 PRINC_cs2]].
    { assert (apply_subst_ctx s'' (apply_subst_ctx s1 G) = apply_subst_ctx phi G).
      { rewrite <- apply_subst_ctx_compose. eapply new_tv_ctx_apply_subst_lt.
        apply n. intros.
        rewrite apply_compose_equiv. symmetry. eapply PRINC_e2.
        auto.
      }
      rewrite H5.
      rewrite <- PRINC_e1.
      apply SOUND_cs_2. }
    exists s'.
    split.
    + eauto.
    + intros.
      repeat rewrite apply_compose_equiv.
      erewrite <- (new_tv_compose_subst_type s'' s2 s'); eauto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
Defined.
Next Obligation.
  unfold top;
  repeat (intros; splits; eauto); 
  destructs H;
    try split; eauto;
  destructs H0; subst;
    try split; eauto.
  - destruct x0. simpl. destruct p0. simpl in *.
    repeat rewrite apply_subst_ctx_app_ctx.
    eapply new_tv_ctx_app.
    eapply new_tv_s_ctx; eauto.
    eapply new_tv_s_ctx; eauto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    (**
  - destruct x0. simpl. destruct p0. simpl in *.
    repeat rewrite apply_subst_ctx_app_ctx.
    eapply new_tv_s_ctx; eauto.
*)
Defined.
Next Obligation.
  destruct (inferPat p J >>= _); crush;
  rename t3 into s1; 
  rename x0 into tau';
  rename x2 into s2;
  rename t1 into s3;
  rename t2 into J';
  rename x1 into tau''.
  - eapply new_tv_compose_subst; eauto.
    eapply new_tv_compose_subst; eauto.
    eapply new_tv_subst_trans;
    eauto. 
  - econstructor.
    + repeat rewrite apply_compose_equiv.
      repeat rewrite apply_subst_ctx_compose.
      rewrite H7.
      eauto.
    + repeat rewrite apply_compose_equiv.
      repeat rewrite apply_subst_ctx_compose.
      repeat rewrite <- apply_subst_ctx_app_ctx.
      eauto.
  - intro. intros.
    rename x3 into tau0.
    rename H14 into COMPL_e, H13 into SOUND_e.
    rename H9 into SOUND_pe.
    inverts SOUND_pe.
    edestruct COMPL_e as [s' [PRINC_e1 PRINC_e2]].
    { eauto. }
    exists s'.
    split.
    + eauto.
      skip.
    + intros.
      skip.
Defined.      
Next Obligation.
  intros. simpl. unfold top;
  repeat (intros; splits; intros; subst; eauto);
  destruct x0, p0; simpl;
  destructs H0; subst; eauto;
  destructs H; subst; eauto.
  - simpl in *.
    repeat rewrite apply_subst_ctx_app_ctx.
    eapply new_tv_ctx_app.
    eapply new_tv_s_ctx; eauto.
    eapply new_tv_s_ctx; eauto.
  - eapply new_tv_s_ctx; eauto.
    destructs* H1.
    destructs* H1.
    eapply new_tv_compose_subst; eauto.
    eapply new_tv_compose_subst; eauto.
    eapply new_tv_subst_trans; eauto.
  - destruct x2. simpl in *.
    destructs* H1.
  - destruct x2. simpl in *.
    destructs* H1.
    repeat rewrite apply_compose_equiv. 
    eapply new_tv_apply_subst_ty; eauto.
    eapply new_tv_apply_subst_ty; eauto.
    eapply new_tv_subst_trans; eauto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
    Unshelve. auto.
Defined.
Next Obligation.
  destruct (inferPat p J >>= _); crush;
  rename t3 into s1; 
  rename x2 into s2;
  rename t1 into s3;
  rename x1 into tau';
  rename x5 into tau'';
  rename x7 into s4'.
  - eapply new_tv_apply_subst_ty; eauto.
  - eapply new_tv_compose_subst; eauto.
    eapply new_tv_compose_subst; eauto.
    eapply new_tv_subst_trans;
    eauto. omega.
    eapply new_tv_compose_subst; eauto.
    eapply new_tv_compose_subst; eauto.
  - econstructor.
    + econstructor.
      * repeat rewrite apply_compose_equiv.
        repeat rewrite apply_subst_ctx_compose.
        rewrite H7.
        eauto.
      * repeat rewrite apply_compose_equiv.
        repeat rewrite apply_subst_ctx_compose.
        repeat rewrite <- apply_subst_ctx_app_ctx.
        rewrite <- H22.
        eauto.
    + repeat rewrite apply_subst_ctx_compose in *.
      repeat rewrite apply_compose_equiv.
      repeat rewrite apply_compose_equiv in H18.
      eauto.
  - skip.
Defined.
 
Print Assumptions W.