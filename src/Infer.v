Set Implicit Arguments.

Require Import LibTactics.
Require Import Sublist.
Require Import Context.
Require Import ListIds.
Require Import Schemes.
Require Import Rename.
Require Import Disjoints.
Require Import Unify.
Require Import Gen.
Require Import Arith.Arith_base.
Require Import Typing.
Require Import List.

(** * State monad creator *)

Record tc_state := mkState {next_tvar : id}.

(** * Infer monadic type and it's operators *)

Definition Infer (A : Type) := tc_state -> option (tc_state * A)%type.

Definition ret (A : Type) (x : A) : Infer A := fun s => Some (s,x).

Definition failT (A : Type) : Infer A := fun s => None.

Definition bind (A B : Type) (c : Infer A) (c' : A -> Infer B) : Infer B :=
  fun s =>
    match c s with
    | None => None
    | Some (s',v) => c' v s'            
    end.

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
Definition fresh : Infer ty :=
  fun s => match s with
          mkState n=> Some (mkState (1 + n), var n)
        end.

(** Gives a list of bound ids *)
Fixpoint list_bounds_ids_aux (sigma : schm) (g : list id) : list id :=
  match sigma with
  | sc_gen i => if in_list_id i g then g else i::g
  | sc_arrow l r => let g' := (list_bounds_ids_aux l g) in (list_bounds_ids_aux r g')
  | _ => nil
  end.

Definition list_bounds_ids (sigma :schm) := list_bounds_ids_aux sigma nil.

(** Gives a type that is a (new) instance of a scheme *)
Definition schm_inst_dep : forall (sigma : schm), Infer ({tau : ty | is_schm_instance tau sigma}).
  refine(fix schm_inst_dep (sigma : schm) :
           Infer ({tau : ty | is_schm_instance tau sigma}) :=
           match list_bounds_ids sigma  with
           | lv =>
             s <- mapM (fun _ => fresh) lv ;
             match apply_inst_subst s sigma as y' return
                   apply_inst_subst s sigma = y' ->
                   Infer ({tau : ty | is_schm_instance tau sigma}) with
             | Error_schm => fun H0 => (failT _) 
             | Some_schm tau => fun H => (ret (exist _ tau _))
             end _
           end).
  unfold is_schm_instance.
  exists s.
  auto.
  auto.
Defined.

Definition  look_dep : forall (x : id) (G : ctx), Infer {sigma | in_ctx x G = Some sigma}.
  refine (fix look' (x : id) (G : ctx) : Infer {sigma | in_ctx x G = Some sigma} :=
            match G with
            | nil => failT _
            | (y, sigma) :: G' => if eq_id_dec x y then ret (exist _ sigma _)
                                 else re <- look' x G' ;
                                 match re with
                                 | exist _ sig _ => ret (exist _ sig _)
                                 end
            end).
  subst. simpl.
  destruct (eq_id_dec y y).
  auto.
  intuition.
  simpl.
  destruct (eq_id_dec y x).
  symmetry in e0.
  intuition.
  auto.
Qed.

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

Definition infer_dep : forall (e : term) (G : ctx),
    Infer ({tau : ty & {s : substitution | has_type (apply_subst_ctx s G) e tau}}).
  refine (fix infer_dep (e : term) (G : ctx) :
            Infer ({tau : ty & {s : substitution | has_type (apply_subst_ctx s G) e tau}}) :=
            match e with
            | const_t x =>
              const_dep <- look_const_dep x G ;
              match const_dep as y with 
              | existT _ (sc_con i) (exist _ j P) => ret (existT _ (con i) (exist _ nil _))
              | existT _ _ E => failT _
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
              taus <- infer_dep e ((x, ty_to_schm alpha) :: G) ;
              match taus with
              | (existT _ tau (exist _ s' p)) =>
                ret (existT _ ( (arrow (apply_subst s' alpha) tau)) (exist _ s' _))
              end 
            | app_t l rho =>
              taus <- infer_dep l G ;
              match taus with
              | existT _ tau (exist _ s p) => 
                taus' <- infer_dep rho (apply_subst_ctx s G) ;
                match taus' with
                | existT _ tau' (exist _ s' p') => 
                  alpha <- fresh ;
                  match unify_simple_dep (apply_subst s' tau) (arrow tau' alpha) with
                  | existT _ c (inleft _ (exist _ x HS)) => ret (existT _ (apply_subst x alpha) (exist _ (s ++ s' ++ x) _))
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
    eapply var_ht.
    rewrite apply_subst_ctx_nil.
    apply pS.
    apply A.
  - clear infer_dep taus taus' s1 s0 s2 s3.
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
  - clear infer_dep taus taus' s0 s1.
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
  - clear infer_dep s taus.
    simpl in p.
    rewrite ty_to_subst_schm in p.
    eapply lam_ht.
    apply p.
  - clear infer_dep.
    rewrite apply_subst_ctx_nil.
    econstructor. 
    destruct P.
    assumption.
Defined.

Definition runInfer_id e g i := infer_dep e g (mkState i).
Definition runInfer e g := infer_dep e g (mkState 0).

Compute runInfer (var_t 0) nil.

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
