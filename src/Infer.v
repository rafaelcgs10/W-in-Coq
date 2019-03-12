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
  end.

Ltac crushAssumptions := (repeat (simpl in *; crush)) ; simpl in *; try inversionExist; auto; try omega; sort.

(** Gives a list of bound ids *)
Fixpoint list_bounds_ids_aux (sigma : schm) (g : list id) : list id :=
  match sigma with
  | sc_gen i => if in_list_id i g then g else i::g
  | sc_arrow l r => let g' := (list_bounds_ids_aux l g) in (list_bounds_ids_aux r g')
  | _ => nil
  end.

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

Definition list_bounds_ids (sigma :schm) := list_bounds_ids_aux sigma nil.

Fixpoint compute_subst (i : id) (l : list ty) : substitution :=
  match l return substitution with
  | nil => nil
  | t :: l' => (i, t) :: compute_subst (S i) l'
  end.

Lemma list_ty_and_id_inv : forall lt_st : list ty,
    {lt_st1 : (list ty) | lt_st1 = lt_st}.
Proof.
intros lt_st; exists lt_st; auto.
Qed.

Ltac destructMatch :=
  match goal with
    | [ |- context[match ?a with  | _ => _ end] ] => edestruct a
  end.

Ltac tryChange := 
  match goal with
    | [ |- ?e ] => change e
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

Program Definition schm_inst_dep (sigma : schm) :
  @HoareState id (@top id) (ty * inst_subst)
              (fun i r f => f = i + (max_gen_vars sigma) /\ apply_inst_subst (snd r) sigma = Some_schm (fst r) /\
              compute_inst_subst i (max_gen_vars sigma) = (snd r)) :=
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
  splits.
  rewrite <- H1.
  omega.
  simpl in *.
  assumption.
  reflexivity.
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
Admitted.

Lemma t_is_app_T_aux : forall (sigma : schm) (tau tau' : ty) (s : substitution) (p : nat) (st : id) (x : list ty),
    new_tv_schm sigma st -> max_gen_vars sigma <= p ->
    apply_inst_subst (compute_inst_subst st p) sigma = Some_schm tau ->
    apply_inst_subst x (apply_subst_schm s sigma) = Some_schm tau' ->
    tau' = apply_subst ((compute_subst st x) ++ s) tau.
Proof.
  Admitted.


Lemma not_in_domain_compute : forall (sg : list ty) (x st : id), x < st ->
 id_in_subst x (compute_subst st sg) = None.
Admitted.

Lemma apply_app_compute_subst :
 forall (s0 : substitution) (st i : id) (sg : list ty),
 i < st -> apply_subst (compute_subst st sg ++ s0) (var i) = apply_subst s0 (var i).
Proof.
intros; apply apply_subst_app1.
apply not_in_domain_compute; auto.
Qed.

Lemma new_tv_ctx_implies_new_tv_schm : forall (G : ctx) (sigma : schm) (st x : id),
    in_ctx x G = Some sigma -> new_tv_ctx G st -> new_tv_schm sigma st.
Proof.
  Admitted.

Lemma apply_compute_gen_subst : forall (i : id) (sigma : schm) (p : nat) i_s,
    {tau : ty | apply_inst_subst i_s sigma = Some_schm tau}.
Admitted.

Definition completeness (e : term) (G : ctx) (tau : ty) (s : substitution) (st : id) :=
  forall (tau' : ty) (phi : substitution),
    has_type (apply_subst_ctx phi G) e tau' -> 
    exists s', tau' = apply_subst s' tau /\
    (forall x : id, x < st -> apply_subst phi (var x) = apply_subst (s ++ s') (var x)).

Definition getSub {e G} (h : {t : ty & {s : substitution | has_type (apply_subst_ctx s G) e t}}) : substitution :=
  match h with
  | existT _ _ (exist _ s _) => s
  end.

Definition getTy{e G} (h : {t : ty & {s : substitution | has_type (apply_subst_ctx s G) e t}}) : ty :=
  match h with
  | existT _ t (exist _ _ _) => t
  end.

(** Gives you a fresh variable *)
Program Definition fresh : @HoareState id (@top id) id (fun i x f => S i = f /\ i = x) := fun n => exist _ (Some (n, S n)) _.

Lemma new_tv_schm_Succ : forall sigma i, new_tv_schm sigma i -> new_tv_schm sigma (S i).
Proof.
  intros.
  induction sigma;
  inversion H; econstructor; auto; try omega.
Qed.

Lemma new_tv_ctx_Succ : forall G i, new_tv_ctx G i -> new_tv_ctx G (S i).
Proof.
  intros.
  induction H.
  - econstructor.
  - econstructor.
    auto.
    apply new_tv_schm_Succ.
    auto.
Qed.

Program Definition addFreshCtx (G : ctx) (x : id) : @HoareState id (fun i => new_tv_ctx G i) (id * ctx) (fun i r f => new_tv_ctx (snd r) f) :=
  alpha <- fresh ;
    ret (alpha, ((x, ty_to_schm (var alpha)) :: G)).
Next Obligation.
  split; intros;
  unfold top; auto.
Defined.
Next Obligation.
  econstructor.
  apply new_tv_ctx_Succ; auto.
  econstructor. auto.
Defined.

Program Definition unify (tau1 tau2 : ty) : @HoareState id (@top id) substitution (fun i r f => i = f) :=
  match unify_simple_dep tau1 tau2 with
  | existT _ c (inleft _ (exist _ x HS)) => ret x
  | existT _ c _ => failT _
  end.
    
Program Definition getProof (G : ctx) : {tau : id | new_tv_ctx G tau}.
Admitted.

Fixpoint sizeTerm e : nat :=
  match e with
  | lam_t _ e => sizeTerm e + 1
  | app_t l r => (max (sizeTerm l) (sizeTerm r)) + 1
  | let_t _ e1 e2 => (max (sizeTerm e1) (sizeTerm e2)) + 1
  | _ => 0
  end.


Lemma add_subst_rewrite_for_modified_stamp : forall (s : substitution) (i : id) (tau : ty), apply_subst ((i, tau)::s) (var i) = tau.
Proof.
  intros.
  simpl.
  mysimp.
Admitted.

Definition remove_subst_by_id' : forall  (i : id) (s : substitution), {s' : substitution | forall u, i <> u -> apply_subst s' (var u) = apply_subst s (var u)}.
  refine (fix remove_subst_by_id' (i : id) (s : substitution) : {s' : substitution |  forall u, i <> u -> apply_subst s' (var u) = apply_subst s (var u)} :=
  match s with
  | nil => exist _ (nil:substitution) _ 
  | (j, t)::s1 => match remove_subst_by_id' i s1 with
                 | exist _ s2 p => match (eq_id_dec i j) with
                                  | left  _ => exist _ s2 _
                                  | right  _ => exist _ ((j, t)::s2) _
                                  end 
                 end 
  end).
  intros; mysimp.
  intros; mysimp.
  Abort.

Fixpoint remove_subst_by_id (i : id) (s : substitution) : substitution :=
  match s with
  | nil => nil
  | (j, t)::s' => if (eq_id_dec i j) then remove_subst_by_id i s' else (j, t)::remove_subst_by_id i s'
  end.                                                                           

Lemma remove_subst_by_id_not_in_subst : forall i s, id_in_subst i (remove_subst_by_id i s) = None.
Proof.
  intros;
  induction s; mysimp.
Qed.

Definition add_subst (i : id) (tau : ty) (s : substitution) (j : id) : substitution :=
  if eq_id_dec i j then (remove_subst_by_id i s) ++ [(i, tau)] else s.

Lemma add_subst_rewrite_for_modified_stamp' : forall (s : substitution) (i : id) (tau : ty),
    apply_subst (add_subst i tau s i) (var i) = apply_subst [(i, tau)] (var i).
  intros.
  pose proof (remove_subst_by_id_not_in_subst i s).
  eapply apply_subst_app1 in H. 
  unfold add_subst.
  mysimp.
  rewrite H.
  mysimp.
Qed.

Lemma add_subst_rewrite_for_unmodified_stamp' : forall (s : substitution) (i : id) (tau : ty) j,
    i <> j ->
    apply_subst (add_subst i tau s j) (var j) = apply_subst s (var j).
  intros.
  unfold add_subst.
  mysimp.
Qed.

(*
Lemma remove_subst_same : forall i s, (proj1_sig (remove_subst_by_id' i s)) = remove_subst_by_id i s.
Proof.
  intros; induction s; mysimp.
  destruct (remove_subst_by_id' i s).
  simpl in *.
  rewrite <- IHs.
  reflexivity.
Qed.

Lemma remove_subst_by_id_if_removed : forall i s j, i <> j -> apply_subst (remove_subst_by_id i s) (var j) = apply_subst s (var j).
Proof.
  intros.
  induction s; mysimp.
  rewrite <- remove_subst_same in *.
  pose proof (remove_subst_by_id' i s).
  destruct H0.
  destruct (remove_subst_by_id' i s).
  simpl in *.
  eapply f_equal in H0 as H0'.
  assert (proj1_sig (remove_subst_by_id' i s) = proj1_sig (exist (fun s' : substitution => apply_subst s' (var i) = var i) s' p)) as HP. 
  {apply H0'. }
  simpl in HP.
  subst.
  inversion p.

  
  eapply proj1_sig in H0.
  simpl in *.
  induction s'.
  
  Admitted.

*)

Lemma add_subst_add_ctx : forall (G : ctx) (s : substitution) (x : id) (st : id) (tau : ty),
       new_tv_ctx G st -> apply_subst_ctx  (add_subst st tau s st) ((x, sc_var st)::G) =  (x, (ty_to_schm tau)) :: (apply_subst_ctx s G).
Admitted.

Program Fixpoint W_hoare (e : term) (G : ctx) {measure (sizeTerm e)} :
  @HoareState id (fun i => new_tv_ctx G i) (ty * substitution)
              (fun i x f =>  has_type (apply_subst_ctx (snd x) G) e (fst x) /\ completeness e G (fst x) (snd x) i) :=
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
              tau_s <- @W_hoare e' (snd alpha_G') _ ;
              ret ((Unify.arrow (apply_subst (snd tau_s) (var (fst alpha_G'))) (fst tau_s)), snd tau_s)

  | app_t l r =>
              tau1_s1 <- @W_hoare l G _ ;
              tau2_s2 <- @W_hoare r (apply_subst_ctx (snd tau1_s1) G) _ ;
              alpha <- fresh ;
              s <- unify (apply_subst (snd tau2_s2) (fst tau1_s1)) (Unify.arrow (fst tau2_s2) (var alpha)) ;
              ret (apply_subst s (var alpha), (snd tau1_s1) ++ (snd tau2_s2) ++ s)

  | let_t x e1 e2  =>
                 tau1_s1 <- @W_hoare e1 G _ ;
                 tau2_s2 <- @W_hoare e2 ((x,gen_ty (fst tau1_s1) (apply_subst_ctx (snd tau1_s1) G) )::(apply_subst_ctx (snd tau1_s1) G)) _ ;
                 ret (fst tau2_s2, (snd tau2_s2) ++ (snd tau1_s1))
  end. 
Next Obligation. (* Case: properties used in const *)
  intros; unfold top; auto.
Defined.
Next Obligation. 
  edestruct (look_dep x G >>= _).
  crushAssumptions.
  split.
  (* Case: var soundness  *)
  - econstructor. rewrite apply_subst_ctx_nil. subst. apply H2. unfold is_schm_instance. exists t1. assumption.
  (* Case: var completeness *)
  - subst.
    unfold completeness.
    intros.
    inversion H0.
    subst.
    destruct (assoc_subst_exists G x phi sigma H3) as [sigma' H3'].
    destruct H3' as [H31  H32].
    destruct H6.
    exists (compute_subst x2 x0 ++ phi).
    split.
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
      simpl.
      symmetry.
      eapply apply_app_compute_subst.
      assumption.
Defined.
Next Obligation. (* Case: properties used in var *)
  intros; unfold top; auto.
Defined.
Next Obligation. 
  edestruct (look_dep x G >>= _).
  crushAssumptions.
  split.
  (* Case: var soundness  *)
  - eapply var_ht. rewrite apply_subst_ctx_nil. subst. apply H2. unfold is_schm_instance. exists t1. assumption.
  (* Case: var completeness *)
  - subst.
    unfold completeness.
    intros.
    inversion H0.
    subst.
    destruct (assoc_subst_exists G x phi sigma H3) as [sigma' H3'].
    destruct H3' as [H31  H32].
    destruct H6.
    exists (compute_subst x2 x0 ++ phi).
    split.
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
      simpl.
      symmetry.
      eapply apply_app_compute_subst.
      assumption.
Defined.
Next Obligation. 
  Admitted.
Next Obligation. (* Case: properties used in lam *)
  splits; auto.
  intros; splits; auto.
  intros; auto.
  unfold top; auto.
Defined.
Next Obligation. (* Case: lam soundness  *)
  simpl.
  destruct (W_hoare e' (((x, sc_var x0)) :: G) _ >>= _).
  simpl.
  crushAssumptions.
  assert (has_type (apply_subst_ctx t1 G) (lam_t x e') (Unify.arrow (apply_subst t1 (var x0)) x1)) as Hsound.
  {
    subst.
    simpl in H0.
    rename t1 into s'.
    rename x1 into tau.
    assert (sc_var x0 = ty_to_schm (var x0)).
    { reflexivity. }
    rewrite H1 in H0.
    rewrite ty_to_subst_schm in H0.
    econstructor.
    assumption. }
  split.
  - apply Hsound.
  - subst.
    clear W_hoare.
    unfold completeness. 
    intros.
    inversion_clear H1.
    cut (exists s' : substitution,
            tau'0 = apply_subst s' x1 /\
            (forall x' : id, x' < S x0 -> apply_subst (add_subst x0 tau phi x') (var x') = apply_subst s' (apply_subst t1 (var x')))).
    intros.
    destruct H1; auto.
    destruct H1; auto.
    exists x2.
    splits.
    rewrite apply_subst_arrow.
    fequals.
    
    erewrite <- H4.
    (* aqui *)
    symmetry.
    assert (apply_subst [(x0, tau)] (var x0) = tau). { mysimp. }
    rewrite <- H5 at 2.
    rewrite add_subst_rewrite_for_modified_stamp'.
    reflexivity.
    auto.

    intros.
    rewrite apply_subst_append.
    erewrite <- H4; auto.
    symmetry.
    erewrite add_subst_rewrite_for_unmodified_stamp'; auto.
    omega.

    unfold completeness in H3.
    edestruct H3.
    erewrite add_subst_add_ctx. 
    apply H2. assumption.

    (* aqui *)

    exists x2.
    destruct H1.
    split. intros; eauto.
    intros.
    apply H4 in H5 as H4'.
    erewrite <- apply_subst_append.
    apply lt_n_Sm_le in H5.
    apply le_lt_eq_dec in H5.
    destruct H5.
    erewrite <- H4'.
    erewrite add_subst_rewrite_for_unmodified_stamp'; auto.
    unfold add_subst.
    mysimp.
    erewrite add_subst_rewrite_for_unmodified_stamp'; auto.
    
    rewrite <- H4'; eauto.
    fequals.
    fequals.
    
    reflexivity.
    rewrite add_subst_rewrite_for_unmodified_stamp'.
    erewrite <- H3.
    rewrite add_subst_rewrite_for_unmodified_stamp'.
    apply H3 in H4.
    assumption.
Defined.
Next Obligation. (* Case: properties used in lam completeness  *)
  simpl.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
    Admitted.
Next Obligation.
    Admitted.
Next Obligation.
    Admitted.
Next Obligation.
    Admitted.
Next Obligation.
    Admitted.
Next Obligation.
    Admitted.


(*
Definition infer_dep : forall (e : term) (G : ctx),
    Infer ({tau : ty & {s : substitution | has_type (apply_subst_ctx s G) e tau /\ completeness e G tau s}}).
  refine (fix infer_dep (e : term) (G : ctx) :
            Infer ({tau : ty & {s : substitution | has_type (apply_subst_ctx s G) e tau /\ completeness e G tau s}}) :=
            match e with
            | const_t x =>
              sigma_dep <- look_dep x G ;
              match sigma_dep with 
              | exist _ sigma pS => 
                etau <- schm_inst_dep sigma ;
                match etau  with
                | exist _ tau A =>  ret (existT _ tau (exist _ nil _))
                end 
              end
            | var_t x =>
              sigma_dep <- look_dep x G ;
              match sigma_dep with 
              | exist _ sigma pS => 
                etau <- schm_inst_dep sigma ;
                match etau  with
                | exist _ tau A =>  ret (existT _ tau (exist _ nil _))
                end 
              end
            | lam_t x e =>
              alpha <- fresh ;
              taus <- infer_dep e ((x, ty_to_schm (var alpha)) :: G) ;
              match taus with
              | (existT _ tau (exist _ s' p)) =>
                ret (existT _ ( (arrow (apply_subst s' (var alpha)) tau)) (exist _ s' _))
              end 
            | app_t l rho =>
              taus <- infer_dep l G ;
              match taus with
              | existT _ tau (exist _ s p) => 
                taus' <- infer_dep rho (apply_subst_ctx s G) ;
                match taus' with
                | existT _ tau' (exist _ s' p') => 
                  alpha <- fresh ;
                  match unify_simple_dep (apply_subst s' tau) (arrow tau' (var alpha)) with
                  | existT _ c (inleft _ (exist _ x HS)) => ret (existT _ (apply_subst x (var alpha)) (exist _ (s ++ s' ++ x) _))
                  | existT _ c _ => failT _
                  end
                end
              end

            | let_t x e1 e2  =>
              taus <- infer_dep e1 G ;
              match taus with
              | existT _ tau (exist _ s p) =>
                taus' <- infer_dep e2 ((x,gen_ty tau (apply_subst_ctx s G) )::(apply_subst_ctx s G)) ;
                match taus' with
                | existT _ tau' (exist _ s' p') => ret (existT _ tau' (exist _ (s ++ s') _))
                end
              end
                
                
            end).
  - clear infer_dep.
    assert (has_type (apply_subst_ctx [] G) (var_t x) tau) as HST1.
    { eapply var_ht. rewrite apply_subst_ctx_nil. apply pS. destruct A.  destruct H. unfold is_schm_instance. exists x0. apply H. }
    split.
    + apply HST1.
    + unfold completeness.
      intros.
      clear etau sigma_dep.
      rename H into HST2.
      rename A into i_s_is_tau_and_compute_gen.
      sort.
      destruct i_s_is_tau_and_compute_gen as [i_s i_s_tau_compute_gen].
      destruct i_s_tau_compute_gen.
      destruct H.
      inversion HST2.
      destruct (assoc_subst_exists G x phi H2) as [sigma'  Hi].
      destruct Hi.
      rewrite H6 in pS.
      inversion pS.
      subst.
      destruct H4.
      apply H1 in H.
      destruct H.
      exists (x1 ++ phi).
      split.
      * auto.
      *



        destruct H3 as [i_s'].
      exists (compute_subst st i_s' ++ phi).
      rewrite inCtx in pS.
      inversion pS.
      subst.
      split.
      *
        eapply t_is_app_T_aux.
        eapply new_tv_ctx_implies_new_tv_schm. 
        apply inCtx. auto.
        skip.
        auto.
      exists (i_s ++ phi).
      split.
      * eapply H1.
        subst.
        
        skip.
        skip.
        (* parei aqui *)
        simpl.

        
      
      rewrite apply_subst_ctx_nil in HST1.
      apply has_type_is_stable_under_substitution with (s:=phi) in HST1 as HST3.
      inversion HST2.
      inversion HST3.
      destruct H3.
      subst. sort.
      destruct A as [i_s].
        destruct (list_ty_and_id_inv (compute_generic_subst st (max_gen_vars sigma))) as [GEN GENC].
        destruct A.
        destruct (apply_compute_gen_subst st sigma (max_gen_vars sigma) x0).
        rewrite e0 in H.
        inversion H.
        subst.
        eapply t_is_app_T_aux.
        eapply new_tv_ctx_implies_new_tv_schm. 
        apply pS; auto.
        auto.
        skip.
        destruct A.
        skip.
        skip.
      * appl


        
      clear etau.
      destruct A.
      sort.
      inversion HST1.
      inversion HST2.
      inversion HST3.
      subst.
      destruct (assoc_subst_exists G x phi H12) as [sigma''  Hi'].
      destruct Hi.
      destruct Hi'.
      sort.
      rewrite H5 in H.
      inversion H.
      rewrite H10 in H6.
      rewrite <- H6 in H3.
      subst. sort.
      
      subst.
      rewrite H1 in pS.
      inversion pS.
      subst.
      sort.
      inversion HST in H.
      subst.
      destruct (assoc_subst_exists G x phi H2) as [sigma''  Hi'].
      destruct Hi'.
      inversion H7.
      assert (sigma'' = sigma). skip.
      subst.

               
      inve

      
      simpl in HST.
      remember A as A'.
      clear HeqA'.
      sort.
      subst.
      exists phi.
      simpl.
      
      exists ((compute_subst st i_s) ++ nil).
      splits.
      
      in
      subst.

      
      inversion H.
      destruct H6.
      destruct a.
      substs.
      rewrite pS in H6.
      inversion H6.
      substs. clear H6. sort.


      pose proof (assoc_subst_exists G x phi H2).
      inversion H6 in pS.
      unfold is_schm_instance in H4.
  - clear infer_dep taus taus' s1 s0 s2 s3.
    split.
    simpl in HS.
    destruct HS.
    destruct H.
    destruct H0.
    rewrite app_assoc.
    rewrite apply_subst_ctx_compose.
    rewrite apply_subst_ctx_compose.
    eapply app_ht with (tau:= apply_subst x tau').
    rewrite <- apply_subst_arrow.
    rewrite <- H.
    apply has_type_is_stable_under_substitution.
    apply has_type_is_stable_under_substitution.
    apply p.
    apply has_type_is_stable_under_substitution.
    apply p'.
    skip.
  - clear infer_dep taus taus' s0 s1.
    skip.
    (**
    destruct p'.
    pose proof exists_renaming_not_concerned_with2 (gen_ty_vars tau (apply_subst_ctx s G))
         (FV_ctx (apply_subst_ctx s G)) (FV_subst s')  as lol.
    destruct lol as [rho].
    inversion r.
    subst.
    pose proof (gen_ty_in_subst_ctx (apply_subst_ctx s G) s' (apply_subst (rename_to_subst rho) tau)) as hip.
    pose proof (renaming_not_concerned_with_gen_vars ) as hip2.
    apply hip2 in r as r'.
    apply hip in r' as r''.
    pose proof (subst_ctx_when_s_disjoint_with_ctx (apply_subst_ctx s G) (rename_to_subst rho)) as top. 
    pose proof (apply_subst_ctx_compose G (rename_to_subst rho) s) as top2.
    apply let_ht with (tau:= apply_subst s' (apply_subst (rename_to_subst rho) tau)).
    rewrite apply_subst_ctx_compose.
    eapply has_type_is_stable_under_substitution.
    erewrite <- top.
    eapply has_type_is_stable_under_substitution.
    apply p.
    rewrite dom_rename_to_subst.
    rewrite H0.
    apply free_and_bound_are_disjoints.
    rewrite apply_subst_ctx_compose.
    rewrite <- gen_ty_in_subst_ctx.
    rewrite <- subst_add_type_scheme.
    rewrite <- gen_alpha4_bis; auto.
    auto.
    *)
  - clear infer_dep s taus.
    split.
    simpl in p.
    rewrite ty_to_subst_schm in p.
    eapply lam_ht.
    apply p.
    skip.
  - clear infer_dep.
    split.
    econstructor.
    rewrite apply_subst_ctx_nil.
    apply pS.
    apply A.
    skip.
Defined.

Definition runInfer_id e g i := infer_dep e g (mkState i).
Definition runInfer e g := infer_dep e g (mkState 0).

Compute runInfer (var_t 0) nil.

*)
