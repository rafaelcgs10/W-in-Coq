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

Unset Program Cases.

(** * A bunch of auxiliary definitions *)

(** Monadic version of a the function [apply_inst_subst]. *)
Program Definition apply_inst_subst_hoare (is_s : inst_subst) (sigma : schm):
  @Infer (@top id) ty (fun i x f => i = f /\ match x with
                                          | inl tau => apply_inst_subst is_s sigma = Some tau
                                          | inr _ => apply_inst_subst is_s sigma = None
                                          end) :=
  match apply_inst_subst is_s sigma with
  | None => failT (SubstFailure' substFail) ty
  | Some tau => ret tau 
  end .

Lemma compute_inst_subst_length : forall i j, length (compute_inst_subst j i) = i.
Proof.
  induction i; intros; crush.
Qed.

Hint Resolve compute_inst_subst_length.

Lemma compute_inst_subst_always_greater : forall sigma x is_s,
    compute_inst_subst x (max_gen_vars sigma) = is_s ->  max_gen_vars sigma <= length is_s.
Proof.
  intros.
  eapply Nat.lt_eq_cases.
  right.
  induction sigma; intros; crush.
Qed.

Hint Resolve compute_inst_subst_always_greater.

Lemma nth_error_is_s_exact_length : forall i is_s, length is_s >= (S i) ->
                                    exists tau, @nth_error ty is_s i = Some tau.
Proof.
  induction i; intros.
  - crush.
    destruct is_s.
    inverts H.
    exists t. reflexivity.
  - destruct is_s.
    inverts H.
    edestruct IHi with (is_s := is_s). 
    simpl in H.
    inversion H.
    omega.
    omega.
    simpl.
    rewrite H0.
    exists x. reflexivity.
Qed.

Hint Resolve nth_error_is_s_exact_length.

Lemma apply_inst_compute_with_inst_subst_exact_length : forall sigma is_s, 
     max_gen_vars sigma <= length is_s ->
      exists tau, apply_inst_subst is_s sigma = Some tau.
Proof.
  induction sigma; intros.
  - simpl. exists (var i). reflexivity.
  - simpl. exists (con i). reflexivity.
  - simpl in *. 
    edestruct nth_error_is_s_exact_length.
    apply H.
    rewrite H0.
    exists x.
    reflexivity.
  - simpl in H.
    assert (length is_s >= max_gen_vars sigma1 /\ length is_s >= max_gen_vars sigma2).
    { assert (Init.Nat.max (max_gen_vars sigma1) (max_gen_vars sigma2) <= length is_s).
      omega.
      eapply Nat.max_lub_iff.
      auto. }
    destruct H0.
    edestruct IHsigma1. apply H0.
    edestruct IHsigma2. apply H1.
    simpl.
    rewrite H2.
    rewrite H3.
    exists (arrow x x0).
    reflexivity.
Qed.

Hint Resolve apply_inst_compute_with_inst_subst_exact_length.

Lemma apply_inst_compute_inst_subst_always_works : forall sigma x, exists tau,
      apply_inst_subst (compute_inst_subst x (max_gen_vars sigma)) sigma = Some tau.
Proof.
  intros.
  edestruct apply_inst_compute_with_inst_subst_exact_length with (is_s:= (compute_inst_subst x (max_gen_vars sigma))) (sigma:=sigma).
  eauto.
  exists x0.
  auto.
Qed.
   
Hint Resolve apply_inst_compute_inst_subst_always_works. 

(** Gives a type that is a (new) instance of a scheme *)
Program Definition schm_inst_dep (sigma : schm) :
  @Infer (@top id) ty
         (fun i x f => f = i + (max_gen_vars sigma) /\ match x with 
                    | inl tau => apply_inst_subst (compute_inst_subst i (max_gen_vars sigma)) sigma = Some tau /\
                                (new_tv_schm sigma i -> new_tv_ty tau f)
                    | inr r => False 
                    end) :=
  match max_gen_vars sigma as y with
  | nmax => 
    st <- get ;
      _ <- put (st + nmax) ;
      tau <- apply_inst_subst_hoare (compute_inst_subst st nmax) sigma ;
      ret tau
  end.
Next Obligation.
  repeat (intros; crush).
Defined.
Next Obligation.
  destruct (apply_inst_subst_hoare (compute_inst_subst x (max_gen_vars sigma)) sigma >>= _);
  crush.
  edestruct apply_inst_compute_inst_subst_always_works with (sigma:=sigma) (x:=x).
  congruence.
  edestruct apply_inst_compute_inst_subst_always_works with (sigma:=sigma) (x:=x).
  congruence.
Defined.

(** Look up function used in algorithm W. *)
Program Definition look_dep (x : id) (G : ctx) :
  @Infer (@top id) schm (fun i k f => i = f /\
                                   match k with
                                   | inl sigma =>  in_ctx x G = Some sigma
                                   | inr _ => in_ctx x G = None
                                   end) :=
  match in_ctx x G with
  | Some sig => ret sig
  | None => failT (@MissingVar' x (missingVar x)) schm
  end.

Set Implicit Arguments.

(** Gives you a fresh variable *)
Program Definition fresh : Infer (@top id) id (fun i x f => match x with
                                                         | inl i' => S i = f /\ i = i'
                                                         | inr r => False
                                                         end) :=
  fun s => (@inl id InferFailure s, S s).

(** Adds a fresh variable to the context *)
Program Definition addFreshCtx (G : ctx) (x : id) (alpha : id):
  @Infer (fun i => new_tv_ctx G i) ctx
         (fun i r f => alpha < i -> match r with
                                | inl G' => (new_tv_ctx G' f /\ f = i /\ new_tv_ty (var alpha) f)
                                | inr r => False
                                end) :=
  ret ((x, ty_to_schm (var alpha)) :: G).
Next Obligation.
  split; intros;
  unfold top; auto.
Defined.

(** Completeness theorem definition. *)
Definition completeness (e : term) (G : ctx) (tau : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution),
    has_type (apply_subst_ctx phi G) e tau' -> 
    exists s', tau' = apply_subst s' tau /\
    (forall x : id, x < st -> apply_subst phi (var x) = apply_subst s' (apply_subst s (var x))).
    
Unset Implicit Arguments.
(** * The algorithm W itself *)

Lemma get_instance_complete : forall e G tau st s2 s1 tau',
    completeness e G tau s1 st ->
    has_type (apply_subst_ctx s2 G) e tau' ->
    exists s', apply_subst (compose_subst s' s2) tau = (apply_subst s2 tau').
Proof.
  intros.
  edestruct H.
  apply H0.
  destruct H1.
  exists x.
  rewrite H1.
  rewrite apply_compose_equiv.
  reflexivity.
Qed.


Unset Program Cases.

Ltac crush_light := repeat (intros; simpl in *; try split; try crush'; subst; auto); try omega.

Program Fixpoint W (e : term) (G : ctx) {struct e} :
  @Infer (fun i => new_tv_ctx G i) (ty * substitution)
         (fun i x f =>  match x with
                    | inl (tau, s) => i <= f /\ new_tv_subst s f /\ new_tv_ty tau f /\
                                     new_tv_ctx (apply_subst_ctx s G) f /\
                                     has_type (apply_subst_ctx s G) e tau /\
                                     completeness e G tau s i 
                    | inr r => ~ exists tau, has_type G e tau
                    end) := 
  match e with

  | const_t x =>
    ret ((con x), nil)

  | var_t x =>
      sigma <- look_dep x G ;
      tau <- schm_inst_dep sigma ;
      ret (tau, nil)

  | lam_t x e' =>
    alpha <- fresh ;
      G' <- @addFreshCtx G x alpha ;
      tau_s <- @W e' G'  ;
      ret ((arrow (apply_subst ((snd tau_s)) (var alpha)) (fst tau_s)), (snd tau_s))

  | app_t l r =>
      tau1_s1 <- W l G ;
      tau2_s2 <- W r (apply_subst_ctx (snd tau1_s1) G)  ;
      alpha <- fresh ;
      s <- unify (apply_subst (snd tau2_s2) (fst tau1_s1)) (arrow (fst tau2_s2) (var alpha)) ;
      ret (apply_subst s (var alpha), compose_subst  (snd tau1_s1) (compose_subst (snd tau2_s2) s))

  | let_t x e1 e2  =>
    tau1_s1 <- @W e1 G  ;
      tau2_s2 <- @W e2 ((x,gen_ty (fst tau1_s1)
                      (apply_subst_ctx (snd tau1_s1) G) )::(apply_subst_ctx (snd tau1_s1) G))  ;
      ret (fst tau2_s2, compose_subst (snd tau1_s1) (snd tau2_s2))


  end. 
Next Obligation.
  unfold top in *.
  repeat (intros; crush).
Defined.
Next Obligation.  (* Case: postcondition of const_t *)
  edestruct (look_dep x G >>= _); crush_light;
  try rename t1 into tau';
  try rename x into st0;
  try rename x1 into st1;
  try rename s into tau.
  - (* Case: var_t soundness *)
    econstructor; eauto. 
    rewrite apply_subst_ctx_nil. eauto.
    unfold is_schm_instance. exists (compute_inst_subst st1 (max_gen_vars tau)).
    assumption.
  (* Case: var_t completeness *)
  - subst.
    unfold completeness.
    intros.
    inversion H3.
    subst.
    inversion H7.
    rename x into is_s.
    destruct (@assoc_subst_exists G st0 phi sigma H5) as [sigma' H5'].
    destruct H5' as [H51  H52].
    destruct H7.
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
  - intros.
    intro.
    destruct H0.
    admit.
    Unshelve. apply nil.
    Unshelve. apply nil.
    Unshelve. apply nil.
    auto.
Admitted.
Next Obligation. 
  unfold top in *.
  repeat (intros; crush).
Defined.
Next Obligation. (* Case: postcondition of lambda  *)
  simpl.
  destruct (W l G  >>= _);
  crush_light;
    clear W;
  try rename i into alpha;
  try rename s into mu;
  try rename t2 into s2;
  try rename t1 into s1;
  try rename H7 into MGU;
  try rename H13 into MGU';
  try rename H15 into MGU'';
  try rename x0 into st1;
  try rename x into st0;
  try rename p0 into tauLR;
  try rename p1 into tauL;
  try rename H6 into COMP_L, H12 into COMP_R.
  - admit.
  (* Subcase : new_tv_subst application *)
    (**
  - fold (apply_subst mu (var alpha)) in *.
    apply new_tv_compose_subst; eauto.
    apply new_tv_compose_subst; eauto.
    eapply MGU'.
    splits; eauto.
    econstructor; eauto.
*)
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
      erewrite <- new_tv_compose_subst_ctx; eauto.
  (** Unification fail case  *)
  - intro.
    rename s1 into s2.
    rename tauLR into tauL.
    rename p into tauLR.
    rename MGU into NO_UNIFIER.
    rename H11 into SOUND_R, H5 into SOUND_L.
    inversion_clear H6.
    rename H into H61, H0 into H62.
    unfold completeness in COMP_L.
    unfold completeness in COMP_R.
    unfold unifier in NO_UNIFIER.