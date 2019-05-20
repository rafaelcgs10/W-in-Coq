(** * The unification algorithm
      This file contains the defintions of constraints for 
      the termination proof, the type specification of the unfication 
      algorithm, the algorithm itself, several lemmas and proofs and
      some functions/interfaces so it's easy to use the unification. *)

Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import LibTactics.
Require Import Coq.Setoids.Setoid.
Require Import Program.
Require Import HoareMonad.
Require Import SimpleTypes.
Require Import Subst.
Require Import NewTypeVariable.
Require Import MyLtacs.
Require Import Varctxt.
Require Import Occurs.
Require Import NonEmptyList.
Require Import WellFormed.

(** The size of a type. This is used in by the termination argument of
    the unification algorithm.  *)

Fixpoint size (t : ty) : nat :=
  match t with
  | arrow l r => 1 + size l + size r
  | appl l r => 1 + size l + size r
  | _ => 1
  end.

(** * The Constraint definition *)

(** We define a constraint as a dependent product of
    a variable context and two types.
    This is needed for a simple termination argument
    for the unification algorithm. **)

Definition constraints := sigT (fun _ : varctxt => (ty * ty)%type).

Definition get_ctxt(c : constraints) : varctxt := let (v,_) := c in v.
Definition get_tys(c : constraints) : (ty * ty)%type := let (_,l) := c in l.
Definition mk_constraints(C : varctxt) (t1 t2 : ty) : constraints := existT _ C (t1, t2).

Definition wf_constraints (c : constraints) :=
  wf_tys (get_ctxt c) (fst (get_tys c)) (snd (get_tys c)).

Definition size_t (t : (ty * ty)) : nat :=
  match t with
  | (t1, t2) => size t1 + size t2
  end.

(** ** Constraint ordering *)

(** A strict order on constraints. Here we use the library definition of lexicographic orderings. *)
Definition constraints_lt : constraints -> constraints -> Prop :=
  lexprod varctxt (fun _ => (ty * ty)%type)
          (fun (x y : varctxt) => length x < length y)
          (fun (x : varctxt) (t t' : (ty * ty)%type) => size_t t < size_t t').

(** A proof that the order is well-founded *)
Definition well_founded_constraints_lt : well_founded constraints_lt :=
  @wf_lexprod varctxt (fun _ : varctxt => (ty * ty)%type)
              (fun (x y : varctxt) => length x < length y)
              (fun (x : varctxt) (l l' : (ty * ty)%type) => size_t l < size_t l')
              (well_founded_ltof varctxt (@length id))
              (fun _ => well_founded_ltof (ty * ty)%type size_t).

(** ** More lemmas about constraints *)
Lemma constraints_mk_inversion : forall t1 t2 C l, get_tys l = (t1, t2) -> get_ctxt l = C ->
                                              l = mk_constraints C (fst (get_tys l)) (snd (get_tys l)).
Proof.
  intros.
  induction l. mysimp.
  destruct p.
  simpl in *.
  unfold mk_constraints.
  subst.
  reflexivity.
Defined.

Hint Resolve constraints_mk_inversion.
Hint Rewrite constraints_mk_inversion:RE.

Hint Resolve left_lex.
Hint Resolve right_lex.

Lemma arrow_lt_constraints1: forall C l1 l2 r1 r2,
    constraints_lt (mk_constraints C l1 l2) (mk_constraints C (arrow l1 r1) (arrow l2 r2)).
Proof.
  intros.
  apply right_lex ; auto.
  simpl. omega.
Qed.

Hint Resolve arrow_lt_constraints1.

Lemma arrow_lt_constraints2: forall C l1 l2 r1 r2,
    constraints_lt (mk_constraints C r1 r2) (mk_constraints C (arrow l1 r1) (arrow l2 r2)).
Proof.
  intros ; apply right_lex ; auto.
  simpl.
  omega.
Defined.

Hint Resolve arrow_lt_constraints2.

Lemma appl_lt_constraints1: forall C l1 l2 r1 r2,
    constraints_lt (mk_constraints C l1 l2) (mk_constraints C (appl l1 r1) (appl l2 r2)).
Proof.
  intros.
  apply right_lex ; auto.
  simpl. omega.
Qed.

Hint Resolve appl_lt_constraints1.

Lemma appl_lt_constraints2: forall C l1 l2 r1 r2,
    constraints_lt (mk_constraints C r1 r2) (mk_constraints C (appl l1 r1) (appl l2 r2)).
Proof.
  intros ; apply right_lex ; auto.
  simpl.
  omega.
Defined.

Hint Resolve appl_lt_constraints2.

(** * Specification of the Unification Algorithm *)

(** ** Definition of unifier *)
Definition unifier (t1 t2 : ty) (s : substitution) : Prop := apply_subst s t1 = apply_subst s t2.

(** A lemma about unifiers and variable substitutions. *)
Lemma unifier_arrowend : forall v t t1 t2 s,
    unifier (apply_subst ((v, t) :: nil) t1) (apply_subst ((v, t) :: nil) t2) s ->
    unifier t1 t2 (compose_subst ((v,t)::nil) s).
Proof.
  intros.
  unfold unifier in *.
  repeat rewrite apply_compose_equiv.
  assumption.
Qed.

Lemma unify_ty : forall t v t' s,
    apply_subst s (var v) = apply_subst s t' ->
    apply_subst s t = apply_subst s (apply_subst ((v, t')::nil) t).
Proof.
  induction t ; intros ; mysimp;
  fequals*.
Qed.

Hint Resolve unify_ty.

Hint Resolve unifier_arrowend.

(** ** The type of the unification algorithm *)

(**
The type of unification algorithm specifies that from well-formed constraints
we can either:

1 - Produce a well-formed substitution s such that it unifies the constraints and s is the
    least of such unifiers.

2 - It returns a proof that no such unifier exists.
    UnifyFailure is defined in HoareMonad file.
 *)

Definition unify_type (c : constraints) :=
  wf_constraints c ->
  ({ s | unifier (fst (get_tys c)) (snd (get_tys c)) s /\ wf_subst (get_ctxt c) s /\
         (forall st, (new_tv_ty (fst (get_tys c)) st /\ new_tv_ty (snd (get_tys c)) st) -> new_tv_subst s st) /\
         forall s', unifier (fst (get_tys c)) (snd (get_tys c)) s' ->
               exists s'', forall v, apply_subst s' (var v) = apply_subst (compose_subst s s'') (var v)})
  + { UnifyFailure (fst (get_tys c)) (snd (get_tys c)) }.

Unset Implicit Arguments.

(** * The unification algorithm itself *)

(** ** Main definition of the unification function *)

(** The unification algorithm is defined by a combinator that performs well-founded recursion
   over a well-founded relation. The constraints_lt is a well founded relation over constraints,
   so, we can use the library combinator for well-founded recursion in order to compute the
   unifier over such constraints. *)

Program Fixpoint unify' (l : constraints) {wf constraints_lt l} : unify_type l :=
  fun wfl => match get_tys l with
          | (var i, t) => match occurs_dec i t with
                         | left _ => inright _ 
                         | right _ => if (eq_ty_dec (var i) t)
                                     then inleft _ (@exist substitution _ nil _) 
                                     else inleft _ (@exist substitution _ ((i, t)::nil) _)
                         end
          | (t, var i) => match occurs_dec i t with
                         | left _ =>  inright _ 
                         | right _ => if (eq_ty_dec (var i) t)
                                     then inleft _ (@exist substitution _ nil _) 
                                     else inleft _ (@exist substitution _ ((i, t)::nil) _)
                         end
          | (con i, con j) => if eq_id_dec i j
                             then inleft _ (@exist substitution _ nil _) 
                             else inright _ 
          | (appl l1 r1, appl l2 r2) => match unify' (mk_constraints (get_ctxt l) l1 l2) _ with
                                         | inright E => inright _
                                         | inleft _ (exist _ s1 HS) =>
                                           match unify' (mk_constraints (minus (get_ctxt l) (dom s1))
                                                                        (apply_subst s1 r1) (apply_subst s1 r2)) _ with
                                           | inright E => inright _
                                           | inleft _ (exist _ s2 HS') =>
                                             inleft _ (@exist substitution _ (compose_subst s1 s2) _)
                                           end
                                         end
          | (arrow l1 r1, arrow l2 r2) => match unify' (mk_constraints (get_ctxt l) l1 l2) _ with
                                         | inright E => inright _
                                         | inleft _ (exist _ s1 HS) =>
                                           match unify' (mk_constraints (minus (get_ctxt l) (dom s1))
                                                                        (apply_subst s1 r1) (apply_subst s1 r2)) _ with
                                           | inright E => inright _
                                           | inleft _ (exist _ s2 HS') =>
                                             inleft _ (@exist substitution _ (compose_subst s1 s2) _)
                                           end
                                         end
          | (arrow _ _, appl _ _) => inright _
          | (appl _ _, arrow _ _) => inright _
          | (appl _ _, con _) => inright _
          | (con  _, appl _ _) => inright _
          | (arrow _ _, con _) => inright _
          | (con  _, arrow _ _) => inright _
          end.
Next Obligation.
  splits; crush.
Defined.
Next Obligation.
  unfold wf_constraints in wfl.
  rewrite <- Heq_anonymous0 in wfl.
  simpl in wfl.
  destruct wfl.
  unfold unifier.
  splits; crush.
  exists s'.
  intros.
  crush.
  Unshelve.
  assumption.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  unfold wf_constraints in wfl.
  rewrite <- Heq_anonymous0 in wfl.
  simpl in wfl.
  destruct wfl.
  unfold unifier.
  splits;
    crush.
  exists s'.
  crush.
  Unshelve. assumption.
Defined.
Next Obligation.
  splits; crush.
  exists s'.
  crush.
Defined.
Next Obligation.
  unfold wf_constraints in wfl.
  rewrite <- Heq_anonymous in wfl.
  simpl in wfl.
  destruct wfl.
  erewrite constraints_mk_inversion with (C := get_ctxt l); eauto.
  repeat rewrite <- Heq_anonymous.
  crush.
Defined.
Next Obligation.
  unfold wf_constraints in *.
  rewrite <- Heq_anonymous in *.
  destruct wfl.
  crush.
Defined.
Next Obligation.
  clear e Heq_anonymous unify'.
  clear n.
  erewrite constraints_mk_inversion with (C := get_ctxt l); eauto.
  destruct wfl.
  repeat rewrite <- Heq_anonymous0 in *.
  induction s1; simpl in *.
  apply right_lex ; eauto.
  repeat rewrite apply_subst_nil.
  simpl. omega.
  apply left_lex ; eauto.
  destruct a; crush.
  apply member_len_minus_lt. eauto.
Defined.
Next Obligation.
  simpl.
  clear Heq_anonymous.
  unfold wf_constraints in *.
  repeat rewrite <- Heq_anonymous0 in wfl.
  simpl in wfl.
  destruct wfl.
  crush.
Defined.
Next Obligation.
  eauto.
Defined.
Next Obligation.
  clear Heq_anonymous Heq_anonymous0 Heq_anonymous1.
  unfold unifier in *.
  splits; crush.
  - inversion H. inversion H0. subst.
    eapply new_tv_compose_subst; eauto. eapply n; eauto.
    splits; eauto. 
  - intros.
    inversion H.
    eapply e0 in u0 as Hl1.
    eapply e0 in H1 as Hl2.
    destruct Hl1 as [ss1 Hl1].
    destruct Hl2 as [ss1' Hl2].
    rewrite apply_subst_fold2 in *.
    eapply ext_subst_var_ty in Hl2 as Hl2'.
    eapply ext_subst_var_ty in Hl2 as Hl2''.
    rewrite Hl2' in H2.
    rewrite Hl2'' in H2.
    repeat rewrite apply_compose_equiv in H2.
    eapply e in H2.
    destruct H2 as [ss2 H2].
    rewrite apply_subst_fold2 in *.
    sort.
    exists ss2.
    rewrite apply_subst_fold2 in *.
    intros.
    rewrite Hl2.
    rewrite apply_compose_assoc_var.
    rewrite apply_compose_equiv.
    rewrite apply_compose_equiv.
    eapply ext_subst_var_ty in H2 as H2'.
    rewrite <- H2'.
    reflexivity.
Defined.
Next Obligation.
  unfold wf_constraints in wfl.
  rewrite <- Heq_anonymous in wfl.
  simpl in wfl.
  destruct wfl.
  erewrite constraints_mk_inversion with (C := get_ctxt l); eauto.
  repeat rewrite <- Heq_anonymous.
  crush.
Defined.
Next Obligation.
  unfold wf_constraints in *.
  rewrite <- Heq_anonymous in *.
  destruct wfl.
  crush.
Defined.
Next Obligation.  clear e Heq_anonymous unify'.
  clear n.
  erewrite constraints_mk_inversion with (C := get_ctxt l); eauto.
  destruct wfl.
  repeat rewrite <- Heq_anonymous0 in *.
  induction s1; simpl in *.
  apply right_lex ; eauto.
  repeat rewrite apply_subst_nil.
  simpl. omega.
  apply left_lex ; eauto.
  destruct a; crush.
  apply member_len_minus_lt. eauto.
Defined.
Next Obligation.
  simpl.
  clear Heq_anonymous.
  unfold wf_constraints in *.
  repeat rewrite <- Heq_anonymous0 in wfl.
  simpl in wfl.
  destruct wfl.
  crush.
Defined.
Next Obligation.
  eauto.
Defined.
Next Obligation.
  clear Heq_anonymous Heq_anonymous0 Heq_anonymous1.
  unfold unifier in *.
  splits; crush.
  - inversion H. inversion H0. subst.
    eapply new_tv_compose_subst; eauto. eapply n; eauto.
    splits; eauto. 
  - intros.
    inversion H.
    eapply e0 in u0 as Hl1.
    eapply e0 in H1 as Hl2.
    destruct Hl1 as [ss1 Hl1].
    destruct Hl2 as [ss1' Hl2].
    rewrite apply_subst_fold2 in *.
    eapply ext_subst_var_ty in Hl2 as Hl2'.
    eapply ext_subst_var_ty in Hl2 as Hl2''.
    rewrite Hl2' in H2.
    rewrite Hl2'' in H2.
    repeat rewrite apply_compose_equiv in H2.
    eapply e in H2.
    destruct H2 as [ss2 H2].
    rewrite apply_subst_fold2 in *.
    sort.
    exists ss2.
    rewrite apply_subst_fold2 in *.
    intros.
    rewrite Hl2.
    rewrite apply_compose_assoc_var.
    rewrite apply_compose_equiv.
    rewrite apply_compose_equiv.
    eapply ext_subst_var_ty in H2 as H2'.
    rewrite <- H2'.
    reflexivity.
Defined.
Next Obligation.
  apply well_founded_constraints_lt.
Defined.


(** * Auxiliary functions so we can use the unification algorithm *)

(** This function gives a list of ids from a type with a proof of wf_ty *)
Definition ids_ty_dep : forall (tau : ty), {l : list id | wf_ty l tau}.
  refine (fix ids_ty_dep (tau : ty) : {t : list id | wf_ty t tau} :=
            match tau with
            | var i => exist _ (i::nil) _
            | appl l r => match ids_ty_dep l with
                          | exist _ g' a => match ids_ty_dep r with
                                           | exist _ g'' b => exist _ (g'++g'') _
                                           end
                          end
            | arrow l r => match ids_ty_dep l with
                          | exist _ g' a => match ids_ty_dep r with
                                           | exist _ g'' b => exist _ (g'++g'') _
                                           end
                          end
            | _ => exist _ nil _
            end);
  crush;
  apply wf_ty_app_comm;
  apply wf_ty_app;
    auto.
Qed.

(** An extension from the above function, but for two types *)
Definition ids_ty_dep2 : forall (tau tau' : ty), {l : list id | wf_ty l tau /\ wf_ty l tau'}.
  refine (fix ids_ty_dep2 (tau tau' : ty) : {t : list id | wf_ty t tau /\ wf_ty t tau'} :=
            match tau,tau' with
            | var i, var j => exist _ (i::j::nil) _
            | appl l r, appl l' r' =>
              match ids_ty_dep2 l l' with
              | exist _ g' a => match ids_ty_dep2 r r' with
                               | exist _ g'' b => exist _ (g'++g'') _
                               end
              end
            | arrow l r, appl l' r' =>
              match ids_ty_dep2 l l' with
              | exist _ g' a => match ids_ty_dep2 r r' with
                               | exist _ g'' b => exist _ (g'++g'') _
                               end
              end
            | appl l r, arrow l' r' =>
              match ids_ty_dep2 l l' with
              | exist _ g' a => match ids_ty_dep2 r r' with
                               | exist _ g'' b => exist _ (g'++g'') _
                               end
              end
            | appl l r, (var i) => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (i::g'++g'') _
                                                    end
                                   end
            | appl l r, (con i) => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (g'++g'') _
                                                    end
                                   end
            | (var i), appl l r => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (i::g'++g'') _
                                                    end
                                   end
            | (con i), appl l r => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (g'++g'') _
                                                    end
                                   end
            | arrow l r, arrow l' r' =>
              match ids_ty_dep2 l l' with
              | exist _ g' a => match ids_ty_dep2 r r' with
                               | exist _ g'' b => exist _ (g'++g'') _
                               end
              end
            | arrow l r, (var i) => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (i::g'++g'') _
                                                    end
                                   end
            | arrow l r, (con i) => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (g'++g'') _
                                                    end
                                   end
            | (var i), arrow l r => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (i::g'++g'') _
                                                    end
                                   end
            | (con i), arrow l r => match ids_ty_dep l with
                                   | exist _ g' a => match ids_ty_dep r with
                                                    | exist _ g'' b => exist _ (g'++g'') _
                                                    end
                                   end
            | var i, _ => exist _ (i::nil) _
            | _, var j => exist _ (j::nil) _
            | _,_ => exist _ nil _
            end);
    mysimp;
    try apply wf_ty_cons;
    try (apply wf_ty_app; auto; fail);
    try (apply wf_ty_app_comm; apply wf_ty_app; auto).
Qed.

(** An interface so unify can work by only providing the two types to be unified *)
Definition unify'' : forall t1 t2 : ty,
    {x & ({ s | unifier t1 t2 s /\ wf_subst x s /\
                (forall st, (new_tv_ty t1 st /\ new_tv_ty t2 st) -> new_tv_subst s st) /\
                forall s', unifier t1 t2 s' ->
                           exists s'', forall v, apply_subst s' (var v) = apply_subst (compose_subst s s'') (var v)})
         + { UnifyFailure t1 t2 }}.
Proof.
  intros.
  pose proof ids_ty_dep2 as dep.
  specialize dep with (tau:=t1) (tau':=t2).
  destruct dep, a.
  exists x.
  refine (unify' (mk_constraints x t1 t2) _).
  unfold wf_constraints.
  simpl.
  split; auto.
Qed.

(** An interface to the Infer monad  *)
Program Definition unify (tau1 tau2 : ty) :
  @Infer (@top id) substitution (fun i mu f =>
                                   i = f /\
                                   (forall s', apply_subst s' tau1 = apply_subst s' tau2 ->
                                          exists s'', forall tau, apply_subst s' tau = apply_subst (compose_subst mu s'') tau) /\
                                   ((new_tv_ty tau1 i /\ new_tv_ty tau2 i) -> new_tv_subst mu i) /\
                                   apply_subst mu tau1 = apply_subst mu tau2) :=
  match unify'' tau1 tau2 as y  with
  | existT _ c (inleft _ (exist _ mu HS)) => ret mu
  | existT _ c (inright _ error) => failT (@UnifyFailure' tau1 tau2 error) substitution
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

Program Fixpoint fold_non_empty_unify (tau : ty) (taus : non_empty_list ty) {struct taus} :
  @Infer (@top id) substitution (fun i mu f =>
                                 i = f /\
                                 (forall tau', ty_in_non_empty_list tau' taus ->
                                          apply_subst mu tau = apply_subst mu tau') ) :=
  match taus with
  | one tau' =>
     mu <- unify tau tau' ;
     ret mu 
  | cons' tau' taus' =>
     mus <- fold_non_empty_unify tau taus' ;
     mu <- unify (apply_subst mus tau) (apply_subst mus tau') ;
     ret (compose_subst mus mu)
  end.
Next Obligation.
  destruct (unify tau tau' >>= _). 
  crush.
  intros.
  cases (eq_ty_dec tau'0 tau'); intuition.
  subst.
  auto.
Defined.
Next Obligation.
  destruct (fold_non_empty_unify tau taus' >>= _). 
  crush.
  intros.
  cases (eq_ty_dec tau'0 tau'); intuition.
  subst.
  repeat rewrite apply_compose_equiv.
  auto.
  apply H2 in H4.
  repeat rewrite apply_compose_equiv.
  rewrite H4.
  reflexivity.
Defined.

Program Fixpoint fold_unify (tau : ty) (taus : list ty) {struct taus} :
  @Infer (@top id) substitution (fun i mu f =>
                                 i = f /\
                                 (forall tau', In tau' taus ->
                                          apply_subst mu tau = apply_subst mu tau') ) :=
  match taus with
  | nil => ret nil
  | tau'::taus' =>
      mus <- fold_unify tau taus' ;
      mu <- unify (apply_subst mus tau) (apply_subst mus tau') ;
      ret (compose_subst mus mu)
  end.
Next Obligation.
  splits; crush.
Defined.
Next Obligation.
  destruct (fold_unify tau taus' >>= _). 
  crush.
  intros.
  destruct H4.
  - subst.
    repeat rewrite apply_compose_equiv.
    auto.
  - apply H2 in H4.
    repeat rewrite apply_compose_equiv.
    rewrite H4.
    reflexivity.
Defined.