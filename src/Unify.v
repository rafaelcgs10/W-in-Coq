Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import LibTactics.
Require Import Coq.Setoids.Setoid.
Require Import Program.
Require Import SimpleTypes.
Require Import Subst.
Require Import NewTypeVariable.
Require Import MyLtacs.
Require Import Varctxt.
Require Import Occurs.
Require Import WellFormed.

(** The size of a type. This is used in by the termination argument of
    the unification algorithm.  **)

Fixpoint size (t : ty) : nat :=
  match t with
    | arrow l r => 1 + size l + size r
    | _ => 1
  end.

(** * The "Real" Constraint definition *)

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

(** ** Termination Proof Lemmas *)

Lemma arrow_lt_size_t : forall l l' r r', size_t (l, l') + size_t (r, r') < size_t (arrow l r, arrow l' r').
Proof.
  intros ; mysimp ; try omega.
Qed.

(** * Specification of the Unification Algorithm *)

Inductive UnifyFailure : ty -> ty -> Prop :=
  | occ_fail  : forall v t, occurs v t -> UnifyFailure (var v) t
  | occ_fail'  : forall v t, occurs v t -> UnifyFailure t (var v)
  | diff_cons : forall n n', n <> n' -> UnifyFailure (con n) (con n')
  | con_arrow   : forall n l r, UnifyFailure (con n) (arrow l r)
  | arrow_con   : forall n l r, UnifyFailure (arrow l r) (con n)
  | arrow_left  : forall l l' r r', UnifyFailure l l' -> UnifyFailure (arrow l r) (arrow l' r')
  | arrow_right  : forall l l' r r' s, UnifyFailure (apply_subst s r) (apply_subst s r') -> UnifyFailure (arrow l r) (arrow l' r') .

Hint Constructors UnifyFailure.

(** ** Definition of a unifier for a list of constraints *)

Definition unifier (t1 t2 : ty) (s : substitution) : Prop := apply_subst s t1 = apply_subst s t2.

(** a simple lemma about unifiers and variable substitutions *)

Lemma unifier_arrowend : forall v t t1 t2 s, unifier (apply_subst ((v, t) :: nil) t1) (apply_subst ((v, t) :: nil) t2) s ->
                         unifier t1 t2 (compose_subst ((v,t)::nil) s).
Proof.
  intros.
  unfold unifier in *.
  repeat rewrite apply_compose_equiv.
  assumption.
Defined.

Lemma unify_ty : forall t v t' s, apply_subst s (var v) = apply_subst s t' ->
                                  apply_subst s t = apply_subst s (apply_subst ((v, t')::nil) t).
Proof.
  induction t ; intros ; mysimp.
  fequals*.
Defined.

Hint Resolve unify_ty.

Hint Resolve unifier_arrowend.

(** * Type of the unification algorithm *)

(*
The type of unification algorithm specifies that from a list of well-formed constraints
we can either:

1 - Produce a well-formed substitution s such that it unifies the constraints and s is the
    least of such unifiers.
2 - It returns a proof that no such unifier exists.

*)

Definition unify_type (c : constraints) := wf_constraints c ->
                    ({ s | unifier (fst (get_tys c)) (snd (get_tys c)) s /\ wf_subst (get_ctxt c) s /\
                           (forall st, (new_tv_ty (fst (get_tys c)) st /\ new_tv_ty (snd (get_tys c)) st) -> new_tv_subst s st) /\
                           forall s', unifier (fst (get_tys c)) (snd (get_tys c)) s' ->
                                 exists s'', forall v, apply_subst s' (var v) = apply_subst (compose_subst s s'') (var v)})
                    + { UnifyFailure (fst (get_tys c)) (snd (get_tys c)) }.

(** * Main definition of the unification function *)

(* The unification algorithm is defined by a combinator that performs well-founded recursion
   over a well-founded relation. The constraints_lt is a well founded relation over constraints,
   so, we can use the library combinator for well-founded recursion in order to compute the
   unifier over such constraints. *)


Unset Implicit Arguments.

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

(*
Definition ids_eliminated (s : substitution) (t1 : ty) : list id := (minus (ids_ty t1) (ids_ty (apply_subst s t1))).
*)

(*
Fixpoint in_list (l : list id) (i : id) :=
  match l with
  | nil => true
  | j::l' => if eq_id_dec j i then true else in_list l' i
  end.
*)

(*
  specialize IHs with (C := remove a C) (t := t).
  rewrite minus_remove in IHs.
  apply IHs; eauto.
  apply wf_ty_remove_minus_inversion in H0. 
*)

(*
Lemma wf_subst_remove_i  : forall i C s, wf_subst (remove i C) s -> ~(member (dom s) i).
Proof.
  intros.
  intro.
  induction s.
  simpl in *.
  assumption.
  simpl in *.
  destruct a.
  simpl in *.
  destruct (eq_id_dec i0 i).
  subst.
  destructs H.
  apply member_remove_false in H.
  assumption.
  destructs H.
  apply wf_subst_remove_inversion in H2.
  auto.
Defined.
*)

(*
Lemma in_list_id_new_tv_tv_lt : forall t i x st, ListIds.in_list_id x (img_ids [(i, t)]) = true -> new_tv_ty t st -> x < st.
Proof.
  induction t; intros; simpl in *; eauto.
  Unshelve. inversion H.
  inversion H.
  inversion H.
Qed.
Hint Resolve in_list_id_new_tv_tv_lt.
*)


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
  | (arrow l1 r1, arrow l2 r2) => match unify' (mk_constraints (get_ctxt l) l1 l2) _ with
                               | inright E => inright _
                               | inleft _ (exist _ s1 HS) =>
                                 match unify' (mk_constraints (minus (get_ctxt l) (dom s1))
                                                              (apply_subst s1 r1) (apply_subst s1 r2)) _ with
                                 | inright E => inright _
                                 | inleft _ (exist _ s2 HS') => inleft _ (@exist substitution _ (compose_subst s1 s2) _)
                                 end
                               end
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
  apply well_founded_constraints_lt.
Defined.

(** * FINAL *)                        
          
Definition projSubs (A : Type) (B : Prop)
           (P : A -> Prop) (u : sumor (sig P) B) : option A :=
  match u with
  | inleft _ (exist _ v _) => Some v
  | inright _ => None
  end.

Definition ids_ty_dep : forall (tau : ty), {l : list id | wf_ty l tau}.
refine (fix ids_ty_dep (tau : ty) : {t : list id | wf_ty t tau} :=
  match tau with
  | var i => exist _ (i::nil) _
  | arrow l r => match ids_ty_dep l with
                | exist _ g' a => match ids_ty_dep r with
                                   | exist _ g'' b => exist _ (g'++g'') _
                                 end
                end
  | _ => exist _ nil _
  end).
  crush.
  crush.
  simpl. 
  splits; eauto.
  apply wf_ty_app_comm.
  apply wf_ty_app;
  auto.
Qed.

Definition ids_ty_dep2 : forall (tau tau' : ty), {l : list id | wf_ty l tau /\ wf_ty l tau'}.
refine (fix ids_ty_dep2 (tau tau' : ty) : {t : list id | wf_ty t tau /\ wf_ty t tau'} :=
  match tau,tau' with
  | var i, var j => exist _ (i::j::nil) _
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

Definition unify : forall t1 t2 : ty,
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

Fixpoint id_in_subst (i : id) (s : substitution) : option ty :=
  match s with
    | nil => None
    | (i', tau)::s' => if eq_id_dec i i' then Some tau else id_in_subst i s'
  end.