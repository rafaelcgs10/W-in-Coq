Set Implicit Arguments.

Require Import LibTactics.
Require Import Sublist.
Require Import Context.
Require Import ListIds.
Require Import Schemes.
Require Import Rename.
Require Import Disjoints.
Require Import Program.
Require Import Unify.
Require Import Gen.
Require Import Arith.Arith_base.
Require Import Typing.
Require Import List.
Require Import NewTypeVariable.

(** * State monad creator *)

Record tc_state := mkState {next_tvar : id}.

(** * Infer monadic type and it's operators *)

Definition Infer (A : Type) := tc_state -> option (tc_state * A)%type.

Definition ret {A : Type} (x : A) : Infer A := fun s => Some (s,x).

Definition failT (A : Type) : Infer A := fun s => None.

Definition bind (A B : Type) (c : Infer A) (c' : A -> Infer B) : Infer B :=
  fun s =>
    match c s with
    | None => None
    | Some (s',v) => c' v s'            
    end.

Lemma mon_left_id : forall (A B : Type) (a : A) (f : A -> Infer B), bind (ret a) f = f a.
  intros.
  reflexivity.
Qed.

Lemma mon_right_id : forall (A : Type) (a : Infer A), (bind a ret) = a.
Admitted.

Notation "x <- c1 ; c2" := (bind c1 (fun x => c2)) 
                            (right associativity, at level 84, c1 at next level).

(** Monadic map *)
Fixpoint mapM (A B : Type) (f : A -> Infer B) (l : list A) : Infer (list B) := 
  match l with
  | nil => ret nil
  | x::xs =>
    x' <- f x ;
      xs' <- mapM f xs ;
      ret (x'::xs')
  end.              

(** Gives you a fresh variable *)
Definition fresh : Infer id :=
  fun s => match s with
          mkState n=> Some (mkState (1 + n), n)
        end.

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

Fixpoint compute_generic_subst (st : id) (n : nat): inst_subst * id :=
  match n with
  | O => (nil, st)
  | S p =>
      match compute_generic_subst (S st) p with
      | (l, st') => (var st :: l, st')
      end
  end.

Definition list_bounds_ids (sigma :schm) := list_bounds_ids_aux sigma nil.

Fixpoint compute_subst (i : id) (l : list ty) : substitution :=
  match l return substitution with
  | nil => nil
  | t :: l' => (i, t) :: compute_subst (S i) l'
  end.


(*
    apply_inst_subst i_s sigma = Some_schm tau ->
    apply_inst_subst i_s' (apply_subst_schm phi sigma) = Some_schm tau' ->
    tau' = apply_subst ((compute_subst st i_s') ++ phi) tau.
*)

Lemma comute_inst_subst_subst : forall i_s s sigma tau tau', are_disjoints (ids_inst_subst i_s) (dom s) -> 
    apply_inst_subst i_s (apply_subst_schm s sigma) = Some_schm tau ->
    apply_inst_subst i_s sigma = Some_schm tau' ->
    apply_subst s tau' = tau.
Proof.
  intros.
Admitted.

(*
Definition compute_gen_subst2 (sigma : schm) :
  Infer ({i_s : list ty & {s : list id | forall sigma i_s' tau phi, (
                                                       are_disjoints s (FV_schm sigma) ->
                                                       dom phi = s -> img phi = i_s' ->
                                                       apply_inst_subst i_s sigma = Some_schm tau ->
                                                       apply_inst_subst i_s' sigma = Some_schm (apply_subst phi tau))}}).
  intros.
  refine (match list_bounds_ids sigma with
  | lv =>
        s <- mapM (fun _ => fresh) lv ;
        match (map (fun i => (var i)) s) with
        | i_s =>  ret (existT _ i_s (exist _ s _))
        end 
  end) . 
  intros.
  assert (i_s = map (fun i : id => var i) s ) as Y.
  { reflexivity. }
  rewrite <- H0 in H.
  pose proof (subst_schm_when_dom_s_disjoint_with_FV_schm phi sigma0 H) as K.
  unfold are_disjoints in H.
  induction i_s.
  - cases s.
    simpl in H.
    symmetry in H.
    Abort.


(** Gives a type that is a (new) instance of a scheme *)
Definition schm_inst_dep : forall (sigma : schm),
    Infer ({tau | exists i_s, apply_inst_subst i_s sigma = (Some_schm tau) /\
           (forall tau' i_s' phi, apply_inst_subst i_s' (apply_subst_schm phi sigma) = Some_schm tau' ->
                             exists s, tau' = apply_subst (s ++ phi) tau )}).
  intros.
  refine(
          match compute_gen_subst2 sigma as y return compute_gen_subst2 sigma = y -> _ with
          | r => fun H1 => 
               i_ss <- r ;
               match i_ss with | existT _ i_s0 (exist _ s0 _) =>
               match apply_inst_subst i_s0 sigma as y' return apply_inst_subst i_s0 sigma = y' -> _ with
               | Error_schm => fun H0 => (failT _) 
               | Some_schm tau => fun H => (ret (exist _ tau _))
               end _  end
           end _).
  exists i_s0.
  split.
  - auto.
  - intros.
    destruct a with (i_s' := i_s') (sigma := sigma) (tau:=tau).
    clear H1 r i_ss s a.
    sort.
    apply H3 in H as H'.
    exists (combine s0 i_s').
    rewrite apply_subst_append.
    symmetry.
    eapply comute_inst_subst_subst.
    apply H0.
    auto.
  - reflexivity.
  - reflexivity.
Defined.
*)

Definition  look_dep : forall (x : id) (G : ctx), Infer {sigma | in_ctx x G = Some sigma}.
  intros.
  refine (match in_ctx x G with
            | None => failT _
            | Some sig => ret (exist _ sig _)
            end).
  reflexivity.
Defined.

Definition  look_const_dep : forall (x : id) (G : ctx), Infer {sigma & {i | in_ctx x G = Some sigma /\ sigma = sc_con i}}.
  refine (fix look' (x : id) (G : ctx) : Infer {sigma & {i | in_ctx x G = Some sigma /\ sigma = sc_con i}} :=
            match G with
            | nil => failT _
            | (y, sigma) :: G' => if eq_id_dec x y then
                                   match sigma as y return sigma = y -> _ with
                                   | sc_con i => fun _ => ret (existT _ sigma (exist _ i _))
                                   | _ => fun _ => failT _
                                   end _
                                 else re <- look' x G' ;
                                 match re with
                                 | existT _ sig (exist _ i P) => ret (existT _ sig (exist _ i _))
                                 end
            end);
  subst; simpl;
  mysimp.
Qed.


Definition getResult (A B : Type) {P} (rs : option (tc_state * (({ti : A & {s : B | P ti s}}))))
  : option (id * A * B) :=
  match rs with
  | None => None
  | Some (mkState i, (existT _ t (exist _ s P))) => Some (i, t ,s)
  end.

Definition getInst (A : Type) {P} (rs : option (tc_state * {x : A | P x}))
  : option A :=
  match rs with
  | None => None
  | Some (mkState i, exist _ s _) => Some s
  end.

Lemma assoc_subst_exists : forall (G : ctx) (i : id) (s : substitution) (sigma : schm),
    in_ctx i (apply_subst_ctx s G) = Some sigma ->
    {sigma' : schm | in_ctx i G = Some sigma' /\ sigma = apply_subst_schm s sigma'}.
Proof.
Admitted.

Definition completeness (e : term) (G : ctx) (tau : ty) (s : substitution) :=
  forall (tau' : ty) (phi : substitution) (st : id),
    has_type (apply_subst_ctx phi G) e tau' -> new_tv_ctx G st ->
    exists s', tau' = apply_subst s' tau /\
    (forall x : id, x < st -> apply_subst phi (var x) = apply_subst (s ++ s') (var x)).

Lemma t_is_app_T_aux : forall (sigma : schm) (tau tau' : ty) (s : substitution) (p : nat) (st : id) (x : list ty),
    new_tv_schm sigma st -> max_gen_vars sigma <= p ->
    apply_inst_subst (fst (compute_generic_subst st p)) sigma = Some_schm tau ->
    apply_inst_subst x (apply_subst_schm s sigma) = Some_schm tau' ->
    tau' = apply_subst ((compute_subst st x) ++ s) tau.
Proof.
  Admitted.

Lemma t_is_app_T_aux' : forall (sigma : schm) (tau tau' : ty) (phi : substitution) (p : nat) (st : id) (i_s i_s' : list ty),
    new_tv_schm sigma st -> max_gen_vars sigma <= p ->
    apply_inst_subst i_s sigma = Some_schm tau ->
    apply_inst_subst i_s' (apply_subst_schm phi sigma) = Some_schm tau' ->
    tau' = apply_subst ((compute_subst st i_s') ++ phi) tau.
Proof.
  Admitted.

Lemma new_tv_ctx_implies_new_tv_schm : forall (G : ctx) (sigma : schm) (st x : id),
    in_ctx x G = Some sigma -> new_tv_ctx G st -> new_tv_schm sigma st.
Proof.
  Admitted.

Lemma list_ty_and_id_inv : forall lt_st : list ty * id,
    {lt_st1 : list ty * id | lt_st1 = lt_st}.
Proof.
intros lt_st; exists lt_st; auto.
Qed.

Lemma apply_compute_gen_subst : forall (i : id) (sigma : schm) (p : nat) i_s,
    {tau : ty | apply_inst_subst i_s sigma = Some_schm tau}.
Admitted.

Fixpoint W (st : id) (e : term) (G : ctx) {struct e} : option (ty * substitution * id) :=
  match e with
  | var_t x => match in_ctx x G with
              | None => None
              | Some sigma =>
                 match compute_generic_subst st (max_gen_vars sigma) with
                 | (l, st') =>
                     match apply_inst_subst l sigma with
                     | Error_schm => None 
                     | Some_schm tau => Some (tau, nil, st')
                     end
                 end
              end
  | _ => Some (var 0, nil, 0)
  end. 

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
