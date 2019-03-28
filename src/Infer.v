Require Import LibTactics.
Require Import Unify.
Require Import Sublist.
Require Import Context.
Require Import ListIds.
Require Import Schemes.
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

Ltac inversionExist :=
  match goal with
    | [ H : exist _ _ _ = exist _ _ _ |- _] => inversion H; clear H
    | [ H : existT _ _ _ = existT _ _ _ |- _] => inversion H; clear H
  end.                                                        

Ltac crush :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H
    | [ H : _ \/ _ |- _] => destruct H
    | [ x : (_ * _)%type |- _ ] => let t := fresh "t" in destruct x as [x t]
    | [ H : (_,_) = (_,_) |- _] => inverts* H
    | [ H : option _ |- _] => destruct H
    | [ H : Some _ = Some _ |- _] => inverts* H
    | [ H : Some _ = None |- _] => congruence
    | [ H : None = Some _ |- _] => congruence
    | [ H : ex _ |- _] => destruct H
    | [ H : sig _ |- _] => destruct H
    | [ H : sigT _ |- _] => destruct H
    | [ H :  let _ := _ in _  |- _] => simpl in H
    | [ H : context[fst (_, _)] |- _] => simpl in H
    | [ H : context[snd (_, _)] |- _] => simpl in H
  end.

Definition BLOCK := True.

Ltac repeat_until_block tac :=
  lazymatch goal with
  | [ |- BLOCK -> _ ] => intros _
  | [ |- _ ] => tac (); repeat_until_block tac
  end.

Ltac crushAssumptions := (repeat (simpl; crush)) ; try inversionExist; try splits;
                         eauto; try (subst; reflexivity); try autorewrite with subst using eauto;
                         try (subst; omega); sort.

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

Fixpoint compute_inst_subst (st : id) (n : nat) : list ty :=
  match n with
  | 0 => nil
  | S n' =>
    match compute_inst_subst (S st) n' with
    | l' => (var st :: l')
    end
  end.

Lemma nth_error_nil : forall i, nth_error (nil : list ty) i = None.
Proof.
  intros.
  induction i; mysimp.
Qed.

Hint Resolve nth_error_nil.

Lemma nth_error_compute_inst_Some : forall i k j, i < k -> nth_error (compute_inst_subst j k) i = Some (var (i + j)).
Proof.
  induction i.
  - intros. destruct k.
    + inversion H.
    + reflexivity.
  - intros. destruct k.
    + inversion H.
    + simpl.
      erewrite IHi.
      fequals.
      fequals.
      omega.
      omega.
Qed.

Hint Resolve nth_error_compute_inst_Some.

Lemma nth_error_compute_inst_None' : forall i j, nth_error (compute_inst_subst j i) i = None.
Proof.
  induction i.
  - intros. reflexivity.
  - intros. simpl. auto.
Qed.

Hint Resolve nth_error_compute_inst_None'.

Lemma nth_error_None_None_cons : forall i (l : list ty) a, nth_error (a :: l) i = None -> nth_error l i = None.
Proof.
  induction i; intros. simpl in *. inversion H.
  simpl in *.
  induction l. reflexivity.
  eapply IHi.
  apply H.
Qed.

Hint Resolve nth_error_None_None_cons.

Lemma nth_error_None_None : forall (l : list ty) i, nth_error l i = None -> nth_error l (S i) = None.
Proof.
  intros.
  induction l.
  erewrite nth_error_nil.
  reflexivity.
  apply nth_error_None_None_cons in H.
  auto.
Qed.

Hint Resolve nth_error_None_None.

Lemma nth_error_None_None_S : forall k i j, nth_error (compute_inst_subst j k) i = None -> nth_error (compute_inst_subst (S j) k) i = None.
Proof.
  induction k; intros. simpl. auto.
  induction i. simpl in *. inversion H.
  simpl. auto.
Qed.

Hint Resolve nth_error_None_None_S.

Lemma nth_error_compute_inst_None : forall i k j, k < i -> nth_error (compute_inst_subst j k) i = None.
Proof.
  induction i.
  - intros. inversion H.
  - intros.
    induction k.
    simpl in *. reflexivity.
    specialize IHi with (j := j) (k := k).
    apply nth_error_None_None_S.
    apply IHi.
    omega.
Qed.

Hint Resolve nth_error_compute_inst_None.

Lemma new_tv_schm_to_new_tv_ty : forall sigma x x0 i, new_tv_schm sigma x ->
                          apply_inst_subst (compute_inst_subst x i) sigma = Some_schm x0 ->
                          new_tv_ty x0 (x + i).
Proof.
  induction sigma; intros; simpl in *; mysimp.
  - inversion H. inversion H0. econstructor. omega.
  - inversion H0.  econstructor.
  - pose proof (Nat.lt_ge_cases i0 i).
    destruct H1.
    + erewrite nth_error_compute_inst_None in H0; auto. 
      inversion H0.
    + apply Nat.lt_eq_cases in H1.
      destruct H1.
      * erewrite nth_error_compute_inst_Some in H0; auto.
        inversion H0. inversion H.
        subst.
        econstructor.
        omega.
      * subst.
        rewrite nth_error_compute_inst_None' in H0.
        inversion H0.
  - inversion H.
    subst.
    cases (apply_inst_subst (compute_inst_subst x i) sigma1).
    cases (apply_inst_subst (compute_inst_subst x i) sigma2).
    inversion H0.
    econstructor; eauto. 
    inversion H0.
    inversion H0.
Qed.

Hint Resolve new_tv_schm_to_new_tv_ty.
      
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
  crushAssumptions.
  intros.
  subst.
  eapply new_tv_schm_to_new_tv_ty; eauto.
Defined.

Program Definition look_dep (x : id) (G : ctx) :
  @HoareState id (@top id) schm (fun i k f => i = f /\ in_ctx x G = Some k) :=
  match in_ctx x G with
  | Some sig => ret sig
  | None => failT _
  end.

Lemma not_in_domain_compute : forall (sg : list ty) (x st : id), x < st ->
 id_in_subst x (compute_subst st sg) = None.
Admitted.

Hint Resolve not_in_domain_compute.
Hint Rewrite not_in_domain_compute.

Lemma new_tv_ctx_implies_new_tv_schm : forall (G : ctx) (sigma : schm) (st x : id),
    in_ctx x G = Some sigma -> new_tv_ctx G st -> new_tv_schm sigma st.
Proof.
  Admitted.

Hint Resolve new_tv_ctx_implies_new_tv_schm.

Lemma assoc_subst_exists : forall (G : ctx) (i : id) (s : substitution) (sigma : schm),
    in_ctx i (apply_subst_ctx s G) = Some sigma ->
    {sigma' : schm | in_ctx i G = Some sigma' /\ sigma = apply_subst_schm s sigma'}.
Proof.
Admitted.

Hint Resolve assoc_subst_exists.

Lemma t_is_app_T_aux : forall (sigma : schm) (tau tau' : ty) (s : substitution) (p : nat) (st : id) (x : list ty),
    new_tv_schm sigma st -> max_gen_vars sigma <= p ->
    apply_inst_subst (compute_inst_subst st p) sigma = Some_schm tau ->
    apply_inst_subst x (apply_subst_schm s sigma) = Some_schm tau' ->
    tau' = apply_subst (compose_subst (compute_subst st x) s) tau.
Proof.
  Admitted.

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

Lemma apply_app_compute_subst :
 forall (s0 : substitution) (st i : id) (sg : list ty),
    i < st -> apply_subst (compose_subst (compute_subst st sg) s0) (var i) = apply_subst s0 (var i).
Proof.
Admitted.

Hint Resolve apply_app_compute_subst.
Hint Rewrite apply_app_compute_subst : subst.

(** Gives you a fresh variable *)
Program Definition fresh : @HoareState id (@top id) id (fun i x f => S i = f /\ i = x) := fun n => exist _ (Some (n, S n)) _.

Lemma new_tv_schm_Succ : forall sigma i, new_tv_schm sigma i -> new_tv_schm sigma (S i).
Proof.
  intros.
  induction sigma;
  inversion H; econstructor; auto.
Qed.

Hint Resolve new_tv_schm_Succ.

Lemma new_tv_ctx_Succ : forall G i, new_tv_ctx G i -> new_tv_ctx G (S i).
Proof.
  intros.
  induction H; econstructor; eauto.
Qed.

Hint Resolve new_tv_ctx_Succ.

Program Definition addFreshCtx (G : ctx) (x : id) : @HoareState id (fun i => new_tv_ctx G i) (id * ctx) (fun i r f => new_tv_ctx (snd r) f /\ f = S i) :=
  alpha <- fresh ;
    ret (alpha, ((x, ty_to_schm (var alpha)) :: G)).
Next Obligation.
  split; intros;
  unfold top; auto.
Defined.
Next Obligation.
  econstructor; auto.
  econstructor; auto.
  econstructor; auto.
Defined.

Fixpoint sizeTerm e : nat :=
  match e with
  | lam_t _ e => sizeTerm e + 1
  | app_t l r => (max (sizeTerm l) (sizeTerm r)) + 1
  | let_t _ e1 e2 => (max (sizeTerm e1) (sizeTerm e2)) + 1
  | _ => 0
  end.

(*
Lemma remove_subst_diff : forall i j s, i <> j -> find_subst (remove_subst_by_id i s) j = find_subst s j. 
Proof.
  intros.
  induction s; mysimp.
Qed.

Hint Resolve remove_subst_diff.
*)
  
Program Definition apply_subst_M (s : substitution) (tau : ty) :
  @HoareState id (@top id) ty (fun i s' f => i = f /\ s' = apply_subst s tau) :=
  ret (apply_subst s tau).

Program Definition unify (tau1 tau2 : ty) : @HoareState id (@top id) substitution
(fun i mu f => i = f /\ (forall s', apply_subst s' tau1 = apply_subst s' tau2 ->
           exists s'', forall tau, apply_subst s' tau = apply_subst (compose_subst mu s'') tau) ) :=
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

Lemma new_tv_schm_apply_subst : forall i tau s sigma, new_tv_schm sigma i ->
                                                  apply_subst_schm ((i, tau) :: s) sigma = apply_subst_schm s sigma.
Proof.
  intros.
  induction sigma;
  mysimp.
  cases (find_subst s i0); eauto;
  try inversion H; omega.
  inversion H. subst.
  fequals; eauto.
Qed.
  
Hint Resolve new_tv_schm_apply_subst.

Lemma new_tv_ctx_apply_subst_ctx : forall st tau s G, new_tv_ctx G st -> apply_subst_ctx ((st, tau) :: s) G = apply_subst_ctx s G.
Proof.
  Admitted.

Hint Resolve new_tv_ctx_apply_subst_ctx.

Lemma add_subst_add_ctx : forall (G : ctx) (s : substitution) (x : id) (st : id) (tau : ty),
    new_tv_ctx G st -> apply_subst_ctx ((st, tau)::s) ((x, sc_var st)::G) =  (x, (ty_to_schm tau)) :: (apply_subst_ctx s G).
Proof.
  intros;
  mysimp.
  rewrite new_tv_ctx_apply_subst_ctx; auto.
Qed.
  
Hint Resolve add_subst_add_ctx.

Lemma new_tv_compose_subst_type : forall (s s1 s2 : substitution) (st : id) (t : ty),
 (forall i : id, i < st -> apply_subst s (var i) = apply_subst s2 (apply_subst s1 (var i))) ->
 new_tv_ty t st -> apply_subst s t = apply_subst s2 (apply_subst s1 t).
Admitted.

Hint Resolve new_tv_compose_subst_type.
Hint Rewrite new_tv_compose_subst_type : subst.

Lemma add_subst_new_tv_ty : forall (s : substitution) (st : id) (tau1 tau2 : ty),
    new_tv_ty tau1 st -> apply_subst ((st, tau2)::s) tau1 = apply_subst s tau1.
  Admitted.

Hint Resolve add_subst_new_tv_ty.
Hint Rewrite add_subst_new_tv_ty : subst.

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

(*
Lemma apply_subst_remove_diff : forall a st s, a <> st -> apply_subst (remove_subst_by_id a s) (var st) = apply_subst s (var st).
Proof.
  intros.
  induction s; mysimp.
Qed.
*)

Lemma new_tv_subst_trans : forall (s : substitution) (i1 i2 : id),
  new_tv_subst s i1 -> i1 <= i2 -> new_tv_subst s i2.
Admitted.

Hint Resolve new_tv_subst_trans.

Lemma new_tv_s_id : forall (st st' : id) (s : substitution),
    new_tv_subst s st -> st' < st -> new_tv_ty (apply_subst s (var st')) st.
Admitted.

Hint Resolve new_tv_s_id.

Lemma new_tv_s_ty : forall (st : id) (s : substitution) (tau : ty),
    new_tv_ty tau st -> new_tv_subst s st -> new_tv_ty (apply_subst s tau) st.
Admitted.

Hint Resolve new_tv_s_ty.

Lemma new_tv_var_id : forall st1 st2 : id, st1 < st2 -> new_tv_ty (var st1) st2.
Admitted.

Hint Resolve new_tv_var_id.

Lemma new_tv_ty_ids : forall (st : id) (tau : ty), new_tv_ty tau st ->
                                               forall x : id, in_list_id x (ids_ty tau) = true -> x < st.
Proof.
  induction tau; intros; simpl in *; mysimp; intuition.
  destruct (eq_id_dec i x); intuition. inversion H. omega.
  apply in_list_id_or_append_inversion in H0.
  destruct H0; inversion H; auto.
Qed.

Hint Resolve new_tv_ty_ids.

Lemma new_tv_ty_trans_le : forall (tau : ty) (st1 st2 : id), new_tv_ty tau st1 -> st1 <= st2 -> new_tv_ty tau st2.
Proof.
  intros.
  Admitted.

Hint Resolve new_tv_ty_trans_le.

Lemma new_tv_compose_subst_ctx : forall (s s1 s2 : substitution) (st : id) (G : ctx),
       (forall x : id, x < st -> apply_subst s (var x) = apply_subst s2 (apply_subst s1 (var x))) ->
       new_tv_ctx G st -> apply_subst_ctx s G = apply_subst_ctx s2 (apply_subst_ctx s1 G).
Admitted.

Lemma s_gen_t_more_general_than_gen_s_t : forall (s : substitution) (G : ctx) (tau : ty),
 more_general (apply_subst_schm s (gen_ty tau G)) (gen_ty (apply_subst s tau) (apply_subst_ctx s G)).
Admitted.

Lemma new_tv_schm_plus : forall sigma st st', new_tv_schm sigma st -> new_tv_schm sigma (st + st').
Proof.
  induction sigma; intros; try econstructor; eauto.
  inversion H. subst. auto.
  inversion H. subst. auto.
Qed.

Hint Resolve new_tv_schm_plus.

Lemma new_tv_ctx_plus : forall G st st', new_tv_ctx G st -> new_tv_ctx G (st + st').
Proof.
  induction G; intros; simpl in *; auto.
  econstructor.
  destruct a.
  inversion H. subst.
  econstructor; eauto.
Qed.

Hint Resolve new_tv_ctx_plus.

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
              alpha_G' <- @addFreshCtx G x ;
              tau_s <- W_hoare e' (snd alpha_G')  ;
              ret ((Unify.arrow (apply_subst ((snd tau_s)) (var (fst alpha_G'))) (fst tau_s)), (snd tau_s))

  | app_t l r =>
              tau1_s1 <- W_hoare l G  ;
              tau2_s2 <- W_hoare r (apply_subst_ctx (snd tau1_s1) G)  ;
              alpha <- fresh ;
              s <- unify (apply_subst (snd tau2_s2) (fst tau1_s1)) (Unify.arrow (fst tau2_s2) (var alpha)) ;
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
  edestruct (look_dep x G >>= _).
  crushAssumptions;
  subst;
  rename x into st0, x2 into st1;
  rename x1 into tau, x3 into tau'.
  - omega.
  - econstructor; simpl; intros; intuition.
  - eauto. 
  - subst. rewrite apply_subst_ctx_nil. eauto.
  - (* Case: var_t soundness *)
    econstructor; eauto. 
    rewrite apply_subst_ctx_nil. eauto.
    unfold is_schm_instance. exists (compute_inst_subst st1 (max_gen_vars tau)). assumption.
  (* Case: var_t completeness *)
  - subst.
    unfold completeness.
    intros.
    inversion H0.
    subst.
    inversion H6.
    rename x into is_s.
    destruct (assoc_subst_exists G st0 phi sigma H3) as [sigma' H3'].
    destruct H3' as [H31  H32].
    destruct H6.
    exists (compose_subst (compute_subst st1 is_s) phi).
    splits.
    + eapply t_is_app_T_aux with (p := max_gen_vars sigma').
      * eapply new_tv_ctx_implies_new_tv_schm. 
       apply H31. auto.
      * reflexivity.
      * rewrite H2 in H31.
        inversion H31. subst.
        assumption.
      * sort.
        rewrite H2 in H31.
        inversion H31.
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
  destruct (W_hoare e' (((x, sc_var x0)) :: G) >>= _).
  simpl.
  crushAssumptions;
  rename x0 into st0, t1 into s, x1 into tau0.
  - subst. omega.
  - subst. assumption.
  - skip.
  - subst. skip.
  - subst.
    clear W_hoare.
    econstructor.
    simpl in H0.
    assert (sc_var st0 = ty_to_schm (var st0)). auto.
    cases (find_subst s st0);
    simpl;
    auto.
  - subst.
      unfold completeness. 
      intros.
      inversion_clear H1.
      fold (apply_subst s (var st0)).
      cut (exists s' : substitution,
              tau'0 = apply_subst s' tau0 /\
              (forall x' : id, x' < S st0 ->  apply_subst (((st0, tau):: phi)) (var x') = apply_subst s' (apply_subst s (var x'))) ) .
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
        erewrite add_subst_rewrite_for_unmodified_stamp; auto; try omega.
      * unfold completeness in H7.
        specialize H7 with (phi := (st0, tau)::phi).
        edestruct H7.
        assert (sc_var st0 = ty_to_schm (var st0)); auto.
        erewrite <- add_subst_add_ctx in H2. 
        apply H2.
        assumption.
        exists x0.
        assumption.
Defined.
Next Obligation. 
  intros; splits; auto.
  intros; splits; auto.
  mysimp.
    Admitted.
Next Obligation.
  destruct (W_hoare l G  >>= _).
  crushAssumptions.
  clear W_hoare.
  - omega.
  - skip.
  - skip.
  - skip.
  - skip.
  - subst.
    clear W_hoare.
    rename H17 into MGU.
    rename x4 into alpha, x into st.
    rename x6 into mu, t1 into s1, t2 into s2.
    rename x2 into tauL, x0 into tauLR.
    rename H6 into COMP_L, H12 into COMP_R.
    unfold completeness. intros.
    rename H6 into SOUND_LR, tau' into tau_r.
    inversion_clear SOUND_LR.
    rename tau into tau_l.
    rename H6 into SOUND_L, H7 into SOUND_R.
    sort.
    apply COMP_L in SOUND_L as PRINC_L.
    destruct PRINC_L as [psi1 PRINC_L].
    destruct PRINC_L as [PRINC_L1 PRINC_L2].
    cut (exists psi2, (tau_l = apply_subst psi2 tauL /\
                 forall x0 : id, x0 < x1 -> apply_subst psi1 (var x0) = apply_subst psi2 (apply_subst s2 (var x0)))).
    intros PRINC_R.
    destruct PRINC_R as [psi2 [PRINC_R1 PRINC_R2]].
    specialize MGU with (s':= ((alpha, tau_r)::psi2)).
    destruct MGU as [s_psi MGU].
    {
      fold (apply_subst ((alpha, tau_r)::psi2) (var alpha)).
      simpl. destruct (eq_id_dec alpha alpha); intuition.
      erewrite (add_subst_new_tv_ty psi2 alpha tauL); eauto.
      rewrite <- PRINC_R1.
      erewrite <- (new_tv_compose_subst_type psi1 s2 ((alpha, tau_r)::psi2) x1 tauLR); eauto.
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
    Admitted.
Next Obligation.
  destruct (W_hoare e1 G >>= _).
  crushAssumptions; subst;
  clear W_hoare.
  - omega.
  - skip.
  - skip.
  - skip.
  - skip.
  - intro. intros.
    rename H12 into SOUND_e2, H5 into SOUND_e1.
    rename H6 into COMP_e1, H13 into COMP_e2.
    rename x into st0, t into st3.
    rename x3 into tau_e2, t2 into s2, x2 into st2.
    rename x1 into tau_e1, t1 into s1, x0 into st1.
    rename H7 into SOUND_let.
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

