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

Fixpoint max_gen_vars (sigma : schm) : nat :=
  match sigma with
  | sc_con _ => 0
  | sc_var _ => 0
  | sc_gen i => S i
  | sc_arrow s1 s2 => max (max_gen_vars s1) (max_gen_vars s2)
  end.

Fixpoint compute_generic_subst (st : id) (n : nat) : list ty  * id:=
  match n with
  | 0 => (nil, st)
  | S n' =>
    match compute_generic_subst (S st) n' with
    | (l', st') => (var st :: l', st')
    end
  end.

Fixpoint compute_subst (i : id) (l : list ty) : substitution :=
  match l return substitution with
  | nil => nil
  | t :: l' => (i, t) :: compute_subst (S i) l'
  end.

(** Gives a type that is a (new) instance of a scheme *)
Program Definition apply_inst_subst_hoare (is_s : inst_subst) (sigma : schm):
  @HoareState id (@top id) ty (fun i r f => i = f /\ apply_inst_subst is_s sigma = Some_schm r) :=
  match apply_inst_subst is_s sigma with
  | Error_schm => failT _
  | Some_schm tau => ret tau 
  end .

      
Program Definition schm_inst_dep (sigma : schm) :
  @HoareState id (@top id) (ty * inst_subst)
              (fun i r f => f = i + (max_gen_vars sigma) /\ apply_inst_subst (snd r) sigma = Some_schm (fst r) /\
              compute_inst_subst i (max_gen_vars sigma) = (snd r) /\ (new_tv_schm sigma i -> new_tv_ty (fst r) f)) :=
    match max_gen_vars sigma as y with
    | nmax => 
       st <- @get id ;
       _ <- @put id (st + nmax) ;
       tau <- apply_inst_subst_hoare (compute_inst_subst st nmax) sigma ;
       ret (tau, (compute_inst_subst st nmax))
    end.
Next Obligation.
  simpl in *.
  destruct (apply_inst_subst_hoare (compute_inst_subst x (max_gen_vars sigma)) sigma >>= _).
  crush.
Defined.

Program Definition look_dep (x : id) (G : ctx) :
  @HoareState id (@top id) schm (fun i k f => i = f /\ in_ctx x G = Some k) :=
  match in_ctx x G with
  | Some sig => ret sig
  | None => failT _
  end.

Lemma assoc_subst_exists : forall (G : ctx) (i : id) (s : substitution) (sigma : schm),
    in_ctx i (apply_subst_ctx s G) = Some sigma ->
    {sigma' : schm | in_ctx i G = Some sigma' /\ sigma = apply_subst_schm s sigma'}.
Proof.
  refine (fix assoc_subst_exists G i s sigma :
            in_ctx i (apply_subst_ctx s G) = Some sigma ->
            {sigma' : schm | in_ctx i G = Some sigma' /\ sigma = apply_subst_schm s sigma'} :=
            (fun PP => match G as G0 return G = G0 -> {sigma' : schm | in_ctx i G = Some sigma' /\ sigma = apply_subst_schm s sigma'} with
            | nil => fun L => exist _ _ _
            | ((j, sigma')::G') => fun L =>  if (eq_id_dec i j) then exist _ sigma' _ else
                                       match assoc_subst_exists G' i s sigma _ with
                                       | exist _ sigma'' _ => exist _ sigma'' _
                                       end
                    end _)  );
  crush.
  Unshelve. auto.
Qed.

Hint Resolve assoc_subst_exists.

Lemma apply_subst_app : forall (s1 s2 : substitution) (st : id),
    find_subst s1 st = None -> apply_subst (s1 ++ s2) (var st) = apply_subst s2 (var st).
Proof.
  induction s1;
  crush.
Qed.

Hint Resolve apply_subst_app.
Hint Rewrite apply_subst_app:RE.

Lemma not_in_domain_compute : forall (is_s : inst_subst) (st0 st1 : id),
    st0 < st1 -> find_subst (compute_subst st1 is_s) st0 = None.
Proof.
  induction is_s; crush.
Qed.

Hint Resolve not_in_domain_compute.
Hint Rewrite not_in_domain_compute:RE.

Lemma apply_app_compute_subst : forall (is_s : inst_subst) (s : substitution) (st0 st1 : id),
       st0 < st1 -> apply_subst ((compute_subst st1 is_s) ++ s) (var st0) = apply_subst s (var st0).
Proof.
  induction is_s;
  crush.
Qed.

Hint Resolve apply_app_compute_subst.
Hint Rewrite apply_app_compute_subst:RE.

Lemma apply_subst_inst_to_ty_to_schm : forall (is_s : inst_subst) (tau : ty),
    apply_inst_subst is_s (ty_to_schm tau) = Some_schm tau.
Proof.
  induction tau; crush.
Qed.

Hint Resolve apply_subst_inst_to_ty_to_schm.
Hint Rewrite apply_subst_inst_to_ty_to_schm:RE.

Lemma assoc_stamp_in_subst_app2 : forall (s1 s2 : substitution) (st : id) (tau : ty),
 find_subst s1 st = Some tau -> find_subst (s1 ++ s2) st = Some tau.
Proof.
  intros. induction s1; crush.
Qed.

Hint Resolve assoc_stamp_in_subst_app2.
Hint Rewrite assoc_stamp_in_subst_app2:RE.

Lemma apply_app : forall (s1 s2 : substitution) (st : id) (tau : ty),
    find_subst s1 st = Some tau -> apply_subst (s1 ++ s2) (var st) = tau.
Proof.
  induction s1; crush.
Qed.

Hint Resolve apply_app.
Hint Rewrite apply_app:RE.

Lemma compute_subst_cons_rwt : forall (st : id) (tau : ty) (sg : inst_subst),
    compute_subst st (tau :: sg) = (st, tau) :: compute_subst (S st) sg.
auto.
Qed.

Hint Resolve compute_subst_cons_rwt.
Hint Rewrite compute_subst_cons_rwt:RE.

Lemma find_subst_id_compute : forall (i : id) (is_s : inst_subst) (st : id) (tau : ty),
    nth_error is_s i = Some tau -> find_subst (compute_subst st is_s) ((st + i)) = Some tau.
Proof.
  induction i; crush.
  destruct is_s; crush.
  destruct is_s. crush.
  rewrite compute_subst_cons_rwt.
  crush.
  rewrite <- Nat.add_succ_comm.
  erewrite IHi; eauto.
Qed.

Hint Resolve find_subst_id_compute.
Hint Rewrite find_subst_id_compute:RE.

Lemma t_is_app_T_aux : forall (sigma : schm) (tau tau' : ty) (s : substitution) (p : nat) (st : id) (x : list ty),
    new_tv_schm sigma st -> max_gen_vars sigma <= p ->
    apply_inst_subst (compute_inst_subst st p) sigma = Some_schm tau ->
    apply_inst_subst x (apply_subst_schm s sigma) = Some_schm tau' ->
    tau' = apply_subst ((compute_subst st x) ++ s) tau.
Proof.
  induction sigma.
  - intros.
    inversion H. subst.
    simpl in H1. inversion H1.
    simpl in H2. fold (apply_subst s (var i)) in H2.
    rewrite apply_subst_inst_to_ty_to_schm in H2.
    inversion H2.
    rewrite apply_app_compute_subst; eauto.
   - crush. 
   - intros. 
     simpl in *.
     rewrite nth_error_compute_inst_Some in *; eauto.
     inversion H1. inversion H. subst.
     cases (nth_error x i).
     inversion H2. subst. clear H2 H1.
     erewrite apply_app; eauto.
     rewrite Nat.add_comm.
     eapply find_subst_id_compute; eauto.
     inversion H2.
   - intros. 
     inversion H. subst.
     simpl in H0. rewrite apply_subst_schm_arrow in H2.
     edestruct (exist_arrow_apply_inst_arrow (compute_inst_subst st p)); eauto.
     destruct H3.
     edestruct (exist_arrow_apply_inst_arrow x); eauto.
     destruct H4. subst.
     apply and_arrow_apply_inst_arrow in H1.
     destruct H1.
     apply and_arrow_apply_inst_arrow in H2.
     destruct H2.
     simpl.
     eapply Nat.max_lub_r in H0 as H0r.
     eapply Nat.max_lub_l in H0 as H0l.
     erewrite <- IHsigma1; eauto.
     erewrite <- IHsigma2; eauto.
Qed.

Hint Resolve t_is_app_T_aux.

Definition completeness (e : term) (G : ctx) (tau : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution),
    has_type (apply_subst_ctx phi G) e tau' -> 
    exists s', tau' = apply_subst s' tau /\
    (forall x : id, x < st -> apply_subst phi (var x) = apply_subst s' (apply_subst s (var x))).

Lemma apply_subst_app1 : forall (s1 s2 : substitution) (st : id),
 find_subst s1 st = None -> apply_subst (compose_subst s1 s2) (var st) = apply_subst s2 (var st).
Proof.
  intros.
  induction s1.
  - mysimp.
  - simpl in *.
    destruct a.
    mysimp.
Qed.

Hint Resolve apply_subst_app1.
Hint Rewrite apply_subst_app1 : subst.

(*
Lemma apply_app_compute_subst :
 forall (s0 : substitution) (st i : id) (sg : list ty),
    i < st -> apply_subst (compose_subst (compute_subst st sg) s0) (var i) = apply_subst s0 (var i).
Proof.
Admitted.

Hint Resolve apply_app_compute_subst.
Hint Rewrite apply_app_compute_subst : subst.
*)

(** Gives you a fresh variable *)
Program Definition fresh : @HoareState id (@top id) id (fun i x f => S i = f /\ i = x) := fun n => exist _ (Some (n, S n)) _.

Program Definition addFreshCtx (G : ctx) (x : id) (alpha : id):
  @HoareState id (fun i => new_tv_ctx G i) ctx (fun i r f => alpha < i -> (new_tv_ctx r f /\ f = i /\ new_tv_ty (var alpha) f)) :=
  ret ((x, ty_to_schm (var alpha)) :: G).
Next Obligation.
  split; intros;
  unfold top; auto.
Defined.

Fixpoint sizeTerm e : nat :=
  match e with
  | lam_t _ e => sizeTerm e + 1
  | app_t l r => (max (sizeTerm l) (sizeTerm r)) + 1
  | let_t _ e1 e2 => (max (sizeTerm e1) (sizeTerm e2)) + 1
  | _ => 0
  end.

Program Definition unify (tau1 tau2 : ty) :
  @HoareState id (@top id) substitution (fun i mu f => i = f /\
                                      (forall s', apply_subst s' tau1 = apply_subst s' tau2 ->
                                             exists s'', forall tau, apply_subst s' tau = apply_subst (compose_subst mu s'') tau) /\
                                      ((new_tv_ty tau1 i /\ new_tv_ty tau2 i) -> new_tv_subst mu i) /\
                                        apply_subst mu tau1 = apply_subst mu tau2) :=
  match Unify.unify tau1 tau2 as y  with
  | existT _ c (inleft _ (exist _ mu HS)) => ret mu
  | existT _ c _ => failT _
  end.
Next Obligation.
  splits; intros; eauto.
  edestruct e; eauto.
  exists x0.
  eapply ext_subst_var_ty.
  intros.
  simpl.
  eauto.
Defined.
    
Lemma add_subst_rewrite_for_modified_stamp : forall (s : substitution) (i : id) (tau : ty),
    (apply_subst ((i, tau)::s) (var i)) = tau.
  intros.
  mysimp.
Qed.

Hint Resolve add_subst_rewrite_for_modified_stamp.

Lemma add_subst_rewrite_for_unmodified_stamp : forall (s : substitution) (i j : id) (tau : ty),
    i <> j -> (apply_subst ((i, tau):: s)) (var j) = apply_subst s (var j).
  intros; induction s; mysimp.
Qed.

Hint Resolve add_subst_rewrite_for_unmodified_stamp.

Lemma img_ids_append_cons : forall a t s, img_ids ((a, t)::s) = ids_ty t ++ img_ids s.
Proof.
  induction t; mysimp.
Qed.

Lemma new_tv_subst_false : forall st s t, new_tv_subst ((st, t) :: s) st -> False.
Proof.
  intros.
  induction s. inversion H.
  specialize H0 with (x:=st).
  simpl in H0.
  destruct (eq_id_dec st st);
  intuition.
  inversion H.
  simpl in H0.
  specialize H0 with (x:=st).
  destruct (eq_id_dec st st); intuition.
Qed.

Hint Resolve new_tv_subst_false.

Lemma new_tv_subst_cons_diff : forall a st t s, a <> st -> new_tv_subst ((a, t) :: s) st -> new_tv_subst s st.
Proof.
  intros.
  econstructor.
  intros.
  unfold FV_subst in H1.
  inversion H0.
  eapply H2.
  simpl.
  destruct (eq_id_dec a x); try contradiction; auto.
  apply in_list_id_or_append_inversion in H1.
  destruct H1.
  apply in_list_id_append1; auto.
  apply in_list_id_append2.
  simpl.
  rewrite img_ids_append_cons.
  apply in_list_id_append2.
  assumption.
Qed.

Hint Resolve new_tv_subst_cons_diff.

Lemma s_gen_t_more_general_than_gen_s_t : forall (s : substitution) (G : ctx) (tau : ty),
 more_general (apply_subst_schm s (gen_ty tau G)) (gen_ty (apply_subst s tau) (apply_subst_ctx s G)).
Admitted.

Unset Implicit Arguments.

Program Fixpoint W_hoare (e : term) (G : ctx) {struct e} :
  @HoareState id (fun i => new_tv_ctx G i) (ty * substitution)
              (fun i x f => i <= f /\ new_tv_subst (snd x) f /\ new_tv_ty (fst x) f /\
               new_tv_ctx (apply_subst_ctx (snd x) G) f /\ has_type (apply_subst_ctx ((snd x)) G) e (fst x) /\ completeness e G (fst x) ((snd x)) i) :=
  match e with
  | const_t x =>
            sigma <- look_dep x G ;
            tau_iss <- schm_inst_dep sigma ;
            ret ((fst tau_iss), nil)

  | var_t x =>
            sigma <- look_dep x G ;
            tau_iss <- schm_inst_dep sigma ;
            ret ((fst tau_iss), nil)

  | lam_t x e' =>
              alpha <- fresh ;
              G' <- addFreshCtx G x alpha ;
              tau_s <- W_hoare e' G'  ;
              ret ((arrow (apply_subst ((snd tau_s)) (var alpha)) (fst tau_s)), (snd tau_s))

  | app_t l r =>
              tau1_s1 <- W_hoare l G  ;
              tau2_s2 <- W_hoare r (apply_subst_ctx (snd tau1_s1) G)  ;
              alpha <- fresh ;
              s <- unify (apply_subst (snd tau2_s2) (fst tau1_s1)) (arrow (fst tau2_s2) (var alpha)) ;
              ret (apply_subst s (var alpha), compose_subst  (snd tau1_s1) (compose_subst (snd tau2_s2) s))

  | let_t x e1 e2  =>
                 tau1_s1 <- W_hoare e1 G  ;
                 tau2_s2 <- W_hoare e2 ((x,gen_ty (fst tau1_s1) (apply_subst_ctx (snd tau1_s1) G) )::(apply_subst_ctx (snd tau1_s1) G))  ;
                 ret (fst tau2_s2, compose_subst (snd tau1_s1) (snd tau2_s2))
  end. 
Next Obligation. (* Case: properties used in var_t *)
  intros; unfold top; auto.
Defined.
Next Obligation.  (* Case: soundness and completeness of var_t *)
  edestruct (look_dep x G >>= _);
  crush;
  rename x into st0, x2 into st1;
  rename x0 into tau', x1 into tau.
  - (* Case: var_t soundness *)
    econstructor; eauto. 
    rewrite apply_subst_ctx_nil. eauto.
    unfold is_schm_instance. exists (compute_inst_subst st1 (max_gen_vars tau)). assumption.
  (* Case: var_t completeness *)
  - subst.
    unfold completeness.
    intros.
    inversion H1.
    subst.
    inversion H7.
    rename x into is_s.
    destruct (assoc_subst_exists G st0 phi sigma H5) as [sigma' H5'].
    destruct H5' as [H51  H52].
    destruct H7.
    exists ((compute_subst st1 is_s) ++ phi).
    splits.
    + eapply t_is_app_T_aux with (p := max_gen_vars sigma'). 
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
      rewrite apply_app_compute_subst.
      reflexivity.
      assumption.
Defined.
Next Obligation. (* Case: properties used in const_t *)
  intros; unfold top; auto.
Defined.
Next Obligation. (* Case: soundness and completeness of cons_t *)
Admitted.
Next Obligation. 
  Admitted.
Next Obligation. (* Case: lam soundness  *)
  simpl.
  destruct (W_hoare e' (((x, sc_var x0)) :: G) >>= _);
  crush; clear W_hoare;
  rename x0 into st0, t1 into s, x1 into tau_r, t into st1.
  - destruct (find_subst s st0).
    + rename t into tau_l.
      econstructor; eauto.
      inversion H4.
      subst.
      eauto.
    + econstructor; eauto.
  - econstructor.
    simpl in H0.
    assert (sc_var st0 = ty_to_schm (var st0)). auto.
    cases (find_subst s st0);
    simpl;
    auto.
  - unfold completeness. 
    intros.
    inversion_clear H2.
    fold (apply_subst s (var st0)).
    cut (exists s' : substitution,
            tau'0 = apply_subst s' tau_r /\
            (forall x' : id, x' < S st0 ->  apply_subst (((st0, tau):: phi)) (var x') = apply_subst s' (apply_subst s (var x'))) ) .
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
      erewrite add_subst_rewrite_for_unmodified_stamp; auto; try omega.
    * unfold completeness in H6.
      specialize H6 with (phi := (st0, tau)::phi).
      edestruct H6.
      assert (sc_var st0 = ty_to_schm (var st0)); auto.
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
Next Obligation.
  destruct (W_hoare l G  >>= _).
  crush;
  clear W_hoare;
  rename H7 into MGU, H13 into MGU', H15 into MGU'';
  rename x4 into alpha, x into st0, x1 into st1;
  rename x3 into mu, t1 into s1, t2 into s2;
  rename H6 into COMP_L, H12 into COMP_R;
  rename x2 into tauL, x0 into tauLR.
  - apply new_tv_compose_subst; eauto.
    apply new_tv_compose_subst; eauto.
    eapply MGU'.
    splits; eauto.
    econstructor; eauto.
  - fold (apply_subst mu (var alpha)).
    subst.
    apply new_tv_s_ty; eauto.
    apply MGU'; eauto.
    splits; eauto.
    econstructor; eauto.
  - subst.
    eapply new_tv_s_ctx; eauto.
    apply new_tv_compose_subst; eauto.
    apply new_tv_compose_subst; eauto.
    eapply MGU'.
    splits; eauto.
    econstructor; eauto.
  - fold (apply_subst mu (var alpha)) in *.
    subst.
    repeat rewrite apply_subst_ctx_compose.
    apply app_ht with (tau := apply_subst mu tauL); eauto.
    rewrite <- MGU'';
    eauto.
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
    + 
      rewrite <- apply_compose_equiv.
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
      apply new_tv_s_ty; auto.
      eapply new_tv_ty_trans_le; eauto. 
    + eapply COMP_R; eauto.
      erewrite <- new_tv_compose_subst_ctx; eauto.
Defined.
Next Obligation.
  unfold top.
  intros; splits; eauto.
  intros; splits; eauto.
  destructs H0;
  try splits; eauto.
Defined.
Next Obligation.
  destruct (W_hoare e1 G >>= _).
  crush;
  clear W_hoare;
  rename H11 into SOUND_e2, H5 into SOUND_e1;
  rename H6 into COMP_e1, H12 into COMP_e2;
  rename x into st0, t into st3;
  rename x3 into tau_e2, t2 into s2, x2 into st2;
  rename x1 into tau_e1, t1 into s1, x0 into st1;
  eauto.
  - eapply new_tv_s_ctx; eauto. 
  -
    pose proof exists_renaming_not_concerned_with2 (gen_ty_vars tau_e1 (apply_subst_ctx s1 G))
         (FV_ctx (apply_subst_ctx s1 G)) (FV_subst s2)  as renaming.
    destruct renaming as [rho renaming].
    inversion renaming.
    subst.
    pose proof (gen_ty_in_subst_ctx (apply_subst_ctx s1 G) s2 (apply_subst (rename_to_subst rho) tau_e1)) as hip.
    pose proof (renaming_not_concerned_with_gen_vars) as hip2.
    apply hip2 in renaming as renaming'.
    apply hip in renaming' as renaming''.
    pose proof (subst_ctx_when_s_disjoint_with_ctx (apply_subst_ctx s1 G) (rename_to_subst rho)) as disj_ctx_subst. 
    pose proof (apply_subst_ctx_compose G (rename_to_subst rho) s1) as rename_compose.
    apply let_ht with (tau:= apply_subst s2 (apply_subst (rename_to_subst rho) tau_e1)).
    rewrite apply_subst_ctx_compose.
    eapply has_type_is_stable_under_substitution.
    erewrite <- disj_ctx_subst.
    eapply has_type_is_stable_under_substitution.
    assumption.
    rewrite dom_rename_to_subst.
    rewrite H6.
    apply free_and_bound_are_disjoints; eauto.
    rewrite apply_subst_ctx_compose; eauto.
    rewrite <- gen_ty_in_subst_ctx; eauto.
    rewrite <- subst_add_type_scheme; eauto.
    rewrite <- gen_alpha4_bis; auto.
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
    (* desafio aqui *)
    eapply typing_in_a_more_general_ctx with
        (G2 := (st0,  (gen_ty (apply_subst psi1 tau_e1) (apply_subst_ctx psi1 (apply_subst_ctx s1 G))))::(apply_subst_ctx psi1 (apply_subst_ctx s1 G))). 
    eapply more_general_ctx_cons. eauto.
    eapply s_gen_t_more_general_than_gen_s_t.
    rewrite <- PRINC_e11.
    erewrite <- new_tv_compose_subst_ctx; eauto.
Defined.

