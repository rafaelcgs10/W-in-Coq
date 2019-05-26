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

(** * The pattern inference *)

Program Fixpoint inferPat (p : pat) (G : ctx) {struct p} :
  @Infer (fun i => new_tv_ctx G i) (ty * ctx * substitution)
         (fun i x f => i <= f /\ new_tv_ctx (snd (fst x)) f /\
                    new_tv_ty (fst (fst x)) f /\
                    has_type_pat (apply_subst_ctx (snd x) G) p (fst (fst x))) :=
  match p with
  | var_p x =>
      alpha <- fresh ;
      G' <- addFreshCtx G x alpha ;
      ret (var alpha, (x, sc_var alpha)::nil, nil)

  | constr_p x ps =>
      sigma <- look_dep x G ;
      _ <- check_is_constructor sigma ;
      tau <- schm_inst_dep sigma ;
      sG <- inferPats ps tau G ;
      ret (apply_subst (fst sG) (return_of_ty tau), apply_subst_ctx (fst sG) (snd sG), fst sG)
  end
with inferPats (pss : pats) (tau: ty) (G : ctx) {struct pss} : 
  @Infer (fun i => new_tv_ctx G i /\ new_tv_ty tau i) (substitution * ctx)
         (fun i x f => i <= f /\ new_tv_ctx (snd x) f /\
                    has_type_pats (apply_subst_ctx (fst x) G) pss (apply_subst (fst x) tau)) :=
       match pss, tau with
       | no_pats, (con i) => ret (nil, G)
       | no_pats, (appl tau1 tau2) => ret (nil, G)
       | (some_pats p ps'), (arrow tau1 tau2) =>
           tauGs <- inferPat p G ; 
           s <- unify (apply_subst (snd tauGs) tau1) (fst (fst tauGs)) ;
           sG <- inferPats ps' (apply_subst s (apply_subst (snd tauGs) tau2)) (apply_subst_ctx s (apply_subst_ctx (snd tauGs) G)) ;
           ret (compose_subst (snd tauGs) (compose_subst s (fst sG)), snd (fst tauGs))
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
  destruct H0.
  subst.
  auto.
Defined.
Next Obligation. (* var_p case *)
  splits; auto.
  econstructor.
Defined.
Next Obligation. 
  unfold top;
    splits; intros;
      try splits; auto;
        intros; auto; splits; eauto.
  destructs H1.
  destructs H0.
  intros; splits; auto.
  destructs H4.
  subst.
  splits; eauto.
Defined.
Next Obligation.
  destruct (look_dep x G >>= _); crush; clear inferPats; sort.
  skip.
  skip.
  rename x2 into tau.
  rename x3 into alpha.
  rename x1 into sigma.
  rename x4 into s.
  rename t2 into G'.
  - destruct sigma.
    (** sc_var *)
    + inverts* H3.
    (** sc_con *)
    + simpl in H0.
      inverts* H0.
      inverts* H7.
      eapply has_type_pat_is_stable_under_substitution; eauto.
      econstructor; eauto.
      exists (nil:inst_subst). reflexivity.
      econstructor.
    (** gen *)
    + inverts* H3.
    (** sc_appl *)
    + simpl in H0.
      cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inversion H0.
      rename t0 into tau1, t1 into tau2.
      rewrite <- H8 in H7.
      inverts* H7.
      eapply has_type_pat_is_stable_under_substitution; eauto.
      econstructor; eauto.
      exists ((compute_inst_subst alpha (max_gen_vars (sc_appl sigma1 sigma2)))).
      simpl.
      rewrite Eq, Eq0.
      rewrite H8. reflexivity.
      econstructor.
      inverts* H0.
      inverts* H0.
    (** sc_arrow *)
    + simpl in H0.
      cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma1).
      cases (apply_inst_subst (compute_inst_subst alpha (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2))) sigma2).
      inversion H0.
      rename t0 into tau1, t1 into tau2.
      erewrite apply_subst_return_of_ty; eauto.
      rewrite <- H8 in H7.
      simpl in H7.
      eapply constr_htp with (sigma:= (apply_subst_schm s (sc_arrow sigma1 sigma2))).
      eauto.
      eauto.
      exists (map_apply_subst_ty s (compute_inst_subst alpha (max_gen_vars (sc_arrow sigma1 sigma2)))).
      eapply subst_inst_subst_type in Eq.
      eapply subst_inst_subst_type in Eq0.
      simpl.
      rewrite Eq, Eq0.
      reflexivity.
      eauto.
      exists ((compute_inst_subst alpha (max_gen_vars (sc_arrow sigma1 sigma2)))).
      simpl.
      rewrite Eq, Eq0.
      reflexivity.
      inverts* H0.
      inverts* H0.
Defined.      
Next Obligation.
  unfold top; auto.
Defined.      
Next Obligation.
  splits; eauto; try econstructor.
Defined.      
Next Obligation.
  unfold top; auto.
Defined.      
Next Obligation.
  splits; eauto; try econstructor.
Defined.      
Next Obligation.
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
  eapply new_tv_s_ctx.
  eapply new_tv_s_ctx.
  eauto.
  eauto.
  skip.
  skip.
  skip.
  Unshelve. auto.
  Unshelve. auto.
Defined.
Next Obligation.
  destruct (inferPat p G >>= _); crush.
  rename x1 into s1, x2 into s2.
  rename t3 into G', t1 into s.
  rename x0 into tau.
  econstructor.
  - repeat erewrite apply_compose_equiv. 
    repeat erewrite apply_subst_ctx_compose. 
    crush.
  - repeat erewrite apply_compose_equiv. 
    repeat erewrite apply_subst_ctx_compose. 
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

Definition completeness (e : term) (G : ctx) (tau : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution) J,
    has_type (apply_subst_ctx phi G) J e tau' -> 
    exists s', tau' = apply_subst s' tau /\
          (forall x : id, x < st -> apply_subst phi (var x) = apply_subst s' (apply_subst s (var x))).
    

(** * The algorithm W itself *)

Program Fixpoint W (e : term) (G J: ctx) {struct e} :
  @Infer (fun i => new_tv_ctx G i) (ty * substitution)
         (fun i x f => i <= f /\ new_tv_subst (snd x) f /\ new_tv_ty (fst x) f /\
                    new_tv_ctx (apply_subst_ctx (snd x) G) f /\
                    has_type (apply_subst_ctx ((snd x)) G) (apply_subst_ctx (snd x) J) e (fst x) /\
                    completeness e G (fst x) ((snd x)) i) :=
  match e with
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
      tau2_s2 <- W r (apply_subst_ctx (snd tau1_s1) G) (apply_subst_ctx (snd tau1_s1) J) ;
      alpha <- fresh ;
      s <- unify (apply_subst (snd tau2_s2) (fst tau1_s1)) (arrow (fst tau2_s2) (var alpha)) ;
      ret (apply_subst s (var alpha), compose_subst  (snd tau1_s1) (compose_subst (snd tau2_s2) s))

  | let_t x e1 e2  =>
      tau1_s1 <- W e1 G J ;
      tau2_s2 <- W e2 ((x,gen_ty (fst tau1_s1)
                      (apply_subst_ctx (snd tau1_s1) G) )::(apply_subst_ctx (snd tau1_s1) G)) (apply_subst_ctx (snd tau1_s1) J) ;
      ret (fst tau2_s2, compose_subst (snd tau1_s1) (snd tau2_s2))

  | case_t e' cs =>
      tau1_s1 <- W e' G J ;
      tau2_s2 <- infer_cases cs (fst tau1_s1) (apply_subst_ctx (snd tau1_s1) G) (apply_subst_ctx (snd tau1_s1) J);
      ret (fst tau2_s2, compose_subst (snd tau1_s1) (snd tau2_s2)) 
  end
with infer_cases (cs : cases) (tau : ty) (G J : ctx) {struct cs} :
       @Infer (fun i => new_tv_ctx G i) (ty * substitution)
              (fun i x f => i <= f /\ has_type_cases (apply_subst_ctx (snd x) G) (apply_subst_ctx (snd x) J) cs (apply_subst (snd x) tau) (fst x)) :=
       match cs with
       | one_case p e =>
          tau_J_s <- inferPat p J ;
          s <- unify (apply_subst (snd tau_J_s) tau) (fst (fst tau_J_s)) ;
          tau_s <- W e (apply_subst_ctx s (apply_subst_ctx (snd tau_J_s) ((snd (fst tau_J_s) ++ G)))) (apply_subst_ctx s (apply_subst_ctx (snd tau_J_s) J)) ;
          ret (fst tau_s, compose_subst (snd tau_J_s) (compose_subst s (snd tau_s)))
       | many_cases p e cs' =>
          tau_J_s <- inferPat p J ;
          s <- unify (apply_subst (snd tau_J_s) tau) (fst (fst tau_J_s)) ;
          tau_s <- W e (apply_subst_ctx s (apply_subst_ctx (snd tau_J_s) ((snd (fst tau_J_s) ++ G)))) (apply_subst_ctx s (apply_subst_ctx (snd tau_J_s) J));

          tau_s' <- infer_cases cs' (apply_subst (compose_subst (snd tau_J_s) (compose_subst s (snd tau_s))) tau)
                 (apply_subst_ctx (compose_subst (snd tau_J_s) (compose_subst s (snd tau_s))) G) 
                 (apply_subst_ctx (compose_subst (snd tau_J_s) (compose_subst s (snd tau_s))) J) ;
          s' <- unify (apply_subst (snd tau_s') (fst tau_s)) (fst tau_s') ;
          ret (apply_subst s' (fst tau_s'), (compose_subst (snd tau_J_s) (compose_subst s (compose_subst (snd tau_s) ((compose_subst (snd tau_s') s'))))))
       end.
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
    inversion H3.
    subst.
    inversion H8.
    rename x into is_s.
    destruct (@assoc_subst_exists G st0 phi sigma H5) as [sigma' H5'].
    destruct H5' as [H51  H52].
    destruct H8.
    exists ((compute_subst st1 is_s) ++ phi).
    splits.
    + eapply new_tv_schm_compute_inst_subst with (p := max_gen_vars sigma'). 
      * eapply new_tv_ctx_implies_new_tv_schm; 
          crush.
      * reflexivity.
      * rewrite H2 in H51.
        inversion H51. subst.
        assumption.
      * sort.
        rewrite H2 in H51.
        inversion H51.
        subst.
        assumption.
    + intros.
      rewrite apply_subst_nil.
      rewrite find_subst_some_apply_app_compute_subst.
      reflexivity.
      assumption. 
Defined.
Next Obligation. 
  splits; intros; unfold top; auto;
    crush. intros. crush. 
  destructs H0; eauto.
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
      inversion H4.
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
    inversion_clear H2.
    fold (apply_subst s (var st0)).
    cut (exists s' : substitution,
            tau'0 = apply_subst s' tau_r /\
            (forall x' : id, x' < S st0 ->  apply_subst (((st0, tau):: phi)) (var x') =
                                      apply_subst s' (apply_subst s (var x'))) ) .
    intros.
    destruct H2; auto.
    destruct H2; auto.
    rename x0 into s'.
    exists s'.
    split.
    * rewrite apply_subst_arrow.
      rewrite H2 at 1.
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
  destructs H0;
    try splits; auto.
Defined.
Next Obligation. (* Case: postcondition of application  *)
  destruct (W l G J >>= _).
  crush;
    clear W;
    rename H7 into MGU, H13 into MGU', H15 into MGU'';
    rename x4 into alpha, x into st0, x1 into st1;
    rename x3 into mu, t1 into s1, t2 into s2;
    rename H6 into COMP_L, H12 into COMP_R;
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
  (* Subcase : new_tv_ctx application *)
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
  destructs H0;
    try splits; eauto.
Defined.
Next Obligation. (* Case : postcondition of let *)
  destruct (W e1 G J >>= _).
  crush;
    clear W;
    rename H11 into SOUND_e2, H5 into SOUND_e1;
    rename H6 into COMP_e1, H12 into COMP_e2;
    rename x into st0, t into st3;
    rename x3 into tau_e2, t2 into s2, x2 into st2;
    rename x1 into tau_e1, t1 into s1, x0 into st1;
    eauto.
  (* Subcase : new_tv_ctx let *)
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
    erewrite <- disj_ctx_subst'.
    eapply has_type_is_stable_under_substitution.
    eauto.
    rewrite dom_rename_to_subst.
    rewrite H6.
    skip.
    rewrite dom_rename_to_subst.
    rewrite H6.
    apply free_and_bound_are_disjoints; eauto.
    rewrite apply_subst_ctx_compose; eauto.
    rewrite <- gen_ty_in_subst_ctx; eauto.
    rewrite <- subst_add_type_scheme; eauto.
    rewrite <- gen_apply_rename_to_subst; eauto.
    rewrite apply_subst_ctx_compose; eauto.
    Unshelve. auto.
    Unshelve. auto.
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
Defined.
Next Obligation.
  unfold top.
  intros; splits; eauto.
  intros; splits; eauto.
  destructs H0;
    try split; eauto.
Defined.
Next Obligation.
  destruct (W e' G J >>= _); crush.
  - skip.
  - skip.
  - skip.
  - econstructor.
    repeat rewrite apply_subst_ctx_compose.
    eapply has_type_is_stable_under_substitution.
    apply H5.
    repeat rewrite apply_subst_ctx_compose.
    assumption.
  - skip.
Defined.
Next Obligation.
  unfold top.
  intros; splits; eauto.
  skip.
  intros; splits; eauto.
  destructs H0;
    try split; eauto.
  skip.
Defined.
Next Obligation.
  destruct (inferPat p J >>= _); crush.
  rename t3 into s1. 
  rename x0 into tau'.
  rename x2 into s2.
  rename t1 into s3.
  rename t2 into J'.
  rename x1 into tau''.
  econstructor.
  - repeat rewrite apply_compose_equiv.
    repeat rewrite apply_subst_ctx_compose.
    rewrite H7.
    apply has_type_pat_is_stable_under_substitution.
    apply has_type_pat_is_stable_under_substitution.
    assumption.
  - repeat rewrite apply_compose_equiv.
    repeat rewrite apply_subst_ctx_compose.
    repeat rewrite <- apply_subst_ctx_app_ctx.
    apply H12.
Defined.      
Next Obligation.
  Admitted.
Next Obligation.
  destruct (inferPat p J >>= _); crush.
  rename t3 into s1. 
  rename x2 into s2.
  rename t1 into s3.
  rename x1 into tau'.
  rename x5 into tau''.
  rename x7 into s4'.
  econstructor.
- econstructor.
  + repeat rewrite apply_compose_equiv.
    repeat rewrite apply_subst_ctx_compose.
    rewrite H7.
    repeat apply has_type_pat_is_stable_under_substitution.
    assumption.
  + repeat rewrite apply_compose_equiv.
    repeat rewrite apply_subst_ctx_compose.
    repeat rewrite <- apply_subst_ctx_app_ctx.
    rewrite <- H18.
    apply has_type_is_stable_under_substitution.
    apply has_type_is_stable_under_substitution.
    apply H12.
 - repeat rewrite apply_subst_ctx_compose in *.
   repeat rewrite apply_compose_equiv.
   repeat rewrite apply_compose_equiv in H15.
   (** aqui *)
    apply has_type_cases_is_stable_under_substitution.
   apply H15.
Defined.
 
Print Assumptions W.