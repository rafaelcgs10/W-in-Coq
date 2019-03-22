Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Program.
Require Import LibTactics.

(** * Type Definitions *)

(** ** Identifier definition *)

(** Identifiers are just natural numbers. This eases the task of equality test *)

Definition id := nat.

(** Decidable equality of identifiers *)

Definition eq_id_dec : forall (v v' : id), {v = v'} + {v <> v'} := eq_nat_dec.

(** Type definition is direct *)

Inductive ty : Set :=
  | var : id -> ty
  | con : id -> ty
  | arrow : ty -> ty -> ty.

(** List of ids in a type *)
Fixpoint ids_ty(tau : ty) : list id :=
  match tau with
  | var i => i::nil
  | arrow l r => (ids_ty l) ++ (ids_ty r) 
  | _ => nil
  end.

(** Decidable equality test for types *)

Definition eq_ty_dec : forall (t t' : ty), {t = t'} + {t <> t'}.
  pose eq_id_dec.
  decide equality.
Defined.

Ltac s :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H
    | [ H : _ \/ _ |- _] => destruct H
    | [ |- context[eq_id_dec ?a ?b] ] => destruct (eq_id_dec a b) ; subst ; try congruence
    | [ |- context[eq_nat_dec ?a ?b] ] => destruct (eq_nat_dec a b) ; subst ; try congruence
    | [ x : (id * ty)%type |- _ ] => let t := fresh "t" in destruct x as [x t]
    | [ H : (_,_) = (_,_) |- _] => inverts* H
    | [ H : Some _ = Some _ |- _] => inverts* H
    | [ H : Some _ = None |- _] => congruence
    | [ H : None = Some _ |- _] => congruence
    | [ |- _ /\ _] => split ~
    | [ H : ex _ |- _] => destruct H
  end.

Ltac mysimp := (repeat (simpl; s)) ; simpl; auto with arith.

(* end hide *)

(** The size of a type. This is used in by the termination argument of
    the unification algorithm.  **)

Fixpoint size (t : ty) : nat :=
  match t with
    | arrow l r => 1 + size l + size r
    | _ => 1
  end.

(** * Context of Type Variables **)

(** Type variables context is the key element to the formalization of the termination
    argument of the unification algorithm. This context is used to store the variables
    that aren't yet solved by the unification. At each step, the unification algorithm
    will solve some variables (thus, the size of the context decreases), or the measure
    of constraints being unified deacreses. *)

Definition varctxt := list id.

(** Definition of when a variable (id) is member of a variable context *)

Fixpoint member (C : varctxt) (i : id) : Prop :=
  match C with
    | nil => False
    | v :: vs => if eq_id_dec v i then True else member vs i
  end.

Lemma member_app : forall c c' i, member c i -> member (c++c') i.
Proof.
  induction c.
  - intros. simpl in *.
    contradiction.
  - intros.
    simpl in *.
    destruct (eq_id_dec a i).
    auto.
    apply IHc.
    auto.
Qed.

Lemma member_app2 : forall c c' i, member c' i -> member (c++c') i.
Proof.
  induction c.
  - intros. simpl in *.
    auto.
  - intros.
    apply IHc in H.
    simpl in *.
    cases (eq_id_dec a i).
    auto.
    auto.
Qed.

(** Decidability of the previous membership relation *)

Definition member_dec : forall C i, {member C i} + {~ member C i}.
  refine (fix member_dec (C : varctxt) (i : id) : {member C i} + {~ member C i} :=
                match C with
                  | nil => right _ _
                  | v :: vs =>
                      match eq_id_dec v i with
                        | left _ => left _ _
                        | right _ =>
                            match member_dec vs i with
                              | left _ => left _ _
                              | right _ => right _ _
                            end
                      end
                end) ; mysimp.
Defined.

Lemma member_app_or : forall c c' i, member (c++c') i -> member c i \/ member c' i.
Proof.
  intros.
  induction c.
  - simpl in *.
    right.
    auto.
  -  simpl in *.
     cases (eq_id_dec a i).
     +  left. auto.
     + apply IHc in H.
       auto.
Qed.

Lemma member_or_app : forall c c' i, member c i \/ member c' i <-> member (c++c') i.
Proof.
  split.
  intros.
  destruct H.
  apply  member_app.
  auto.
  destruct c.
  simpl.
  auto.
  simpl.
  cases (eq_id_dec i0 i).
  auto.
  apply member_app2.
  auto.
  intros.
  apply member_app_or in H.
  auto.
Qed.

Lemma member_app_comm : forall c c' i, member (c'++c) i -> member (c++c') i.
Proof.
  intros.
  apply member_or_app in H.
  destruct H.
  apply member_or_app.
  right. auto.
  apply member_or_app.
  left. auto.
Qed.  

(** * Well Formedness Definitions *)

(** Here we define the concepts of well formed types and constraints. We
    say that a type is well formed if all of its variables are in a variable context.
    Similarly, a constraint is well formed if all of its types are well formed.*)

Fixpoint wf_ty (C : varctxt) (t : ty) : Prop :=
  match t with
    | var v => member C v
    | con _ => True
    | arrow l r => wf_ty C l /\ wf_ty C r
  end.

Lemma wf_ty_cons : forall c a t, wf_ty c t -> wf_ty (a::c) t.
Proof.
  intros.
  induction t.
  - simpl in *.
    destruct (eq_id_dec a i).
    auto.
    auto.
  - auto.
  - simpl in *.
    destruct H.
    split.
    apply IHt1.
    auto.
    apply IHt2.
    auto.
Qed.

Lemma wf_ty_app : forall c' c t, wf_ty c t -> wf_ty (c++c') t.
Proof.
  induction c.
  - intros.
    induction t.
    + simpl in *.
      contradiction.
    + auto.
    + simpl in *.
      split.
      destruct H.
      auto.
      destruct H.
      auto.
  - intros.
    induction t.
    + simpl in *.
      destruct (eq_id_dec a i).
      auto.
      apply member_app.
      auto.
    + auto.
    + simpl in *.
      split.
      destruct H.
      apply IHt1.
      auto.
      apply IHt2.
      destruct H.
      auto.
Qed.
      
Lemma wf_ty_app_comm : forall c c' t, wf_ty (c++c') t -> wf_ty (c'++c) t.
Proof.
  induction c'.
  - intros.
    simpl in *.
    rewrite <- app_nil_end in H.
    auto.
  - intros.
    induction t.
    + apply member_app_comm in H.
      simpl in *.
      destruct (eq_id_dec a i).
      auto.
      auto.
    + auto.
    + simpl in *.
      destruct H.
      split.
      apply IHt1.
      auto.
      apply IHt2.
      auto.
Qed.

Definition wf_tys (C : varctxt) (t1 t2 : ty)  : Prop := wf_ty C t1 /\ wf_ty C t2.

(** * The "Real" Constraint definition *)

 (** We define a constraint as a dependent product of
    a variable context and a list of constraints.
    This is needed for a simple termination argument
    for the unification algorithm. **)

Definition constraints := sigT (fun _ : varctxt => (ty * ty)%type).

Definition get_ctxt(c : constraints) : varctxt := let (v,_) := c in v.
Definition get_tys(c : constraints) : (ty * ty)%type := let (_,l) := c in l.
Definition mk_constraints(C : varctxt) (t1 t2 : ty) : constraints := existT _ C (t1, t2).

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

(** * Occurs-check test *)

(** A predicate that specifies when a variable v occurs free in a type t *)

Fixpoint occurs (v : id) (t : ty) : Prop :=
  match t with
    | var n => if eq_id_dec n v then True else False
    | con n => False
    | arrow l r => occurs v l \/ occurs v r
  end.

(** Decidability of occurs check test *)

Definition occurs_dec : forall v t, {occurs v t} +  {~ occurs v t}.
  refine (fix occurs_dec v t : {occurs v t} +  {~ occurs v t} :=
            match t with
              | var n =>
                  if eq_id_dec n v then left _ _ else right _ _
              | con n => right _ _
              | arrow l r =>
                  match occurs_dec v l, occurs_dec v r with
                    | left _, left _ => left _ _
                    | left _, right _ => left _ _
                    | right _, left  _ => left _ _
                    | right _, right _ => right _ _
                  end
            end) ; mysimp ; intuition.
Defined.

(** * Substitutions *)

(** A operation for substitute all the ocurrences of variable x in t2 by t1. *)
Definition substitution := list (id * ty).

Fixpoint find_subst (s : substitution) (i : id) : option ty :=
  match s with
    | nil => None
    | (v,t') :: s' => if (eq_id_dec v i) then Some t' else find_subst s' i
  end.

Fixpoint apply_subst (s : substitution) (t : ty) : ty :=
  match t with
  | arrow l r => arrow (apply_subst s l) (apply_subst s r)
  | var i => match find_subst s i with
            | None => var i
            | Some t' => t'
            end
  | con i => con i
  end.

(** Removing a variable from a variable context *)

Fixpoint remove (v : id) (ctx : varctxt) : varctxt :=
  match ctx with
    | nil => nil
    | y :: ys => if eq_id_dec y v then remove v ys else y :: (remove v ys)
  end.

(** Suppose that a type t is well formed with respect to a variable context ctx and
    the variable x is free in t,
    if we substitute x for u and u is well formed with respecto to ctx - {x},
    we get a type that is well formed with respect to ctx - {x}.
    This is formalized by the lemma subst_remove. *)

Lemma subst_remove' : forall x t ctx, member ctx t -> x <> t -> member (remove x ctx) t.
Proof.
  induction ctx ; mysimp.
Qed.

(* begin hide *)

Hint Resolve subst_remove'.

(* end hide *)

Lemma subst_remove : forall t x ctx, wf_ty ctx t -> member ctx x ->
                                     forall u, wf_ty (remove x ctx) u ->
                                               wf_ty (remove x ctx) (apply_subst ((x, u)::nil) t).
Proof.
  induction t ; simpl ; intros ; mysimp.
Qed.

(* begin hide *)

Hint Resolve subst_remove.

(* end hide *)

(** ** Substitution Definitions and Its Well Formedness Predicate *)

(** Substitution and its dom *)

Definition dom (s : substitution) : list id := List.map (@fst id ty) s.
Definition img (s : substitution) : list ty := List.map (@snd id ty) s.
Definition img_ids (s : substitution) : list id := List.concat (List.map ids_ty (img s)).

(** Definition of a  well formed substitution. A substitution is well formed,
    if form each pair (v,t), where v is a variable and t a type, we have that
    v is in a variable context C and t is well formed in the variable context
    C - {v}. *)

Fixpoint wf_subst (C : varctxt) (s : substitution) : Prop :=
  match s with
    | nil => True
    | (v,t) :: s' => member C v /\ wf_ty (remove v C) t /\ wf_subst (remove v C) s'
  end.

(** Removing a list of names from a given variable context. *)

Fixpoint minus (C : varctxt) (xs : list id) : varctxt :=
  match xs with
    | nil => C
    | x :: xs => remove x (minus C xs)
  end.

Lemma remove_comm : forall x y C, remove x (remove y C) = remove y (remove x C).
Proof.
  induction C ; mysimp.
Qed.

Print remove_comm.

Hint Resolve remove_comm.

Lemma minus_remove : forall C2 C1 x, minus (remove x C1) C2 = remove x (minus C1 C2).
Proof.
  induction C2 ; mysimp ; intros ; rewrite IHC2 ; auto.
Qed.

Lemma minus_arrow : forall (C : varctxt) s v t, minus C (dom (s ++ (v,t) :: nil)) = remove v (minus C (dom s)).
Proof.
  induction s ; mysimp ; intros ; mysimp ; rewrite IHs ; auto.
Qed.
(** ** Some Obvious Facts About Substitutions **)

Lemma apply_subst_id : forall t, apply_subst nil t = t.
Proof.
  induction t ; mysimp.
  congruence.
Qed.

Hint Resolve apply_subst_id.
Hint Rewrite apply_subst_id : subst.

Lemma apply_subst_con : forall s n, apply_subst s (con n) = con n.
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_con.
Hint Rewrite apply_subst_con : subst.

Lemma apply_subst_arrow : forall s l r, apply_subst s (arrow l r) = arrow (apply_subst s l) (apply_subst s r).
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_arrow.
Hint Rewrite apply_subst_arrow : subst.

(** ** Substitution composition **)
Fixpoint in_subst_b (i : id) (s : substitution) : bool :=
  match s with
  | nil => false
  | (j, _)::s' => if eq_id_dec i j then true else in_subst_b i s'
  end.

Fixpoint subst_diff (s2 s1 : substitution) : substitution :=
  match s2 with
  | nil => nil
  | (i, t)::s2' => if in_subst_b i s1 then subst_diff s2' s1 else
                    (i, t)::subst_diff s2' s1
  end.

Lemma subst_diff_nill : forall s, subst_diff s nil = s.
Proof.
  induction s; mysimp.
  congruence.
Qed.

Fixpoint apply_subst_list (s1 s2 : substitution) : substitution :=
  match s1 with
  | nil => nil
  | (i, t)::s1' => (i, apply_subst s2 t)::apply_subst_list s1' s2
  end.

Lemma apply_subst_nil : forall t, apply_subst nil t = t.
Proof.
  intros; induction t; mysimp.
  congruence.
Qed.

Hint Resolve apply_subst_nil.
Hint Rewrite apply_subst_nil : subst.

Lemma apply_subst_list_nil : forall s, apply_subst_list s nil = s.
Proof.
  induction s; mysimp.
  rewrite apply_subst_nil.
  congruence.
Qed.

Hint Resolve apply_subst_list_nil.
Hint Rewrite apply_subst_list_nil : subst.

Definition compose_subst (s1 s2 : substitution) :=
    subst_diff s2 s1 ++ apply_subst_list s1 s2.

Lemma compose_subst_nil1 : forall s2, compose_subst nil s2 = s2.
Proof.
  intros; induction s2; mysimp.
  unfold compose_subst.
  rewrite subst_diff_nill.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Hint Resolve compose_subst_nil1.
Hint Rewrite compose_subst_nil1 : subst.

(** ** Some Obvious Facts About Composition **)

Lemma apply_compose_subst_nil1 : forall s t, apply_subst (compose_subst nil s) t = apply_subst s t.
Proof.
  intros; mysimp. autorewrite with subst using congruence.
Qed.

Hint Resolve apply_compose_subst_nil1.
Hint Rewrite apply_compose_subst_nil1 : subst.

Lemma apply_compose_subst_nil2 : forall s t, apply_subst (compose_subst s nil) t = apply_subst s t.
Proof.
  intros; mysimp; induction s; autorewrite with subst using congruence.
  induction t; mysimp.
  repeat rewrite apply_subst_arrow in IHs.
  inversion IHs.
  fequals;
  auto.
Qed.

Hint Resolve apply_compose_subst_nil2.
Hint Rewrite apply_compose_subst_nil2 : subst.


Lemma apply_compose_equiv : forall s2 s1 t, apply_subst (compose_subst s1 s2) t = apply_subst s2 (apply_subst s1 t).
Proof.
  induction s2; intros; mysimp. repeat rewrite apply_compose_subst_nil2.  autorewrite with subst using congruence.
Admitted.

Lemma apply_subst_end : forall s v t t', apply_subst (compose_subst s ((v,t)::nil)) t' = apply_subst ((v, t)::nil) (apply_subst s t').
Proof.
  induction s ; intros; mysimp; repeat rewrite apply_compose_subst_nil1. repeat rewrite apply_subst_nil; try reflexivity.
Admitted.
  
Hint Resolve apply_subst_end.
Hint Rewrite apply_subst_end : subst.

(*
Lemma apply_subst_append : forall s2 s1 t, apply_subst (s1 ++ s2) t = apply_subst s2 (apply_subst s1 t).
Proof.
  induction s2 ; intros ; simpl. rewrite <- app_nil_end ; auto.
  assert (s1 ++ a :: s2 = (s1 ++ (a::nil)) ++ s2).
  rewrite app_ass ; auto. rewrite H. destruct a. rewrite (IHs2 (s1 ++ (i,t0)::nil)).
  rewrite <- apply_subst_end. auto.
Qed.
*)

Lemma member_remove_false : forall i C, member (remove i C) i -> False.
Proof.
  intros.
  induction C;
    mysimp.
  simpl in H.
  cases (eq_id_dec a i). auto.
  simpl in H. cases (eq_id_dec a i); intuition.
Qed.

Lemma wf_ty_var : forall i C, member C i <-> wf_ty C (var i).
Proof.
  split.
  intros.
  induction C.
  inversion H.
  simpl in *.
  mysimp.
  intros.
  induction C.
  inversion H.
  simpl in *.
  mysimp.
Qed.

Lemma wf_ty_var_false : forall i C, wf_ty (remove i C) (var i) -> False.
Proof.
  intros.
  induction C; mysimp.
  simpl in H.
  cases (eq_id_dec a i).
  auto.
  simpl in H.
  cases (eq_id_dec a i); intuition.
Qed.
  
  
Lemma subst_remove_single : forall a C t t0, wf_ty (remove a C) t -> wf_ty C t -> wf_ty C t0 ->
                                     wf_ty (remove a C) (apply_subst ((a, t0)::nil) t).
Proof.
  intros.
  induction t.
  simpl in *. cases (eq_id_dec a i).
  subst. apply member_remove_false in H. contradiction.
  apply wf_ty_var.
  assumption.
  mysimp.
  simpl in *.
  destruct H, H0.
  split;
  auto.
Qed.

Lemma wf_subst_remove_inversion : forall i C s, wf_subst (remove i C) s -> wf_subst C s.
  Admitted.

Lemma wf_subst_last (s : substitution) : forall x t C, wf_subst C s ->
  member (minus C (dom s)) x -> wf_ty (remove x (minus C (dom s))) t ->
    wf_subst C (s ++ (x,t)::nil).
Proof.
  induction s ; simpl ; intros ; mysimp.
  apply (IHs _ _ (remove a C)) ; auto ; rewrite minus_remove ; auto.
Qed.

Hint Resolve wf_subst_last.

Lemma arrowcons (A:Type) : forall (s1 s2:list A) x, s1 ++ x::s2 = (s1 ++ x::nil) ++ s2.
  intros ; rewrite app_ass ; auto.
Qed.

Lemma wf_subst_arrowend : forall C s2 s1,  wf_subst C s1 ->
                                         wf_subst (minus C (dom s1)) s2 ->
                                         wf_subst C (s1 ++ s2).
Proof.
  induction s2 ; simpl ; intros. rewrite <- app_nil_end ; auto.
  mysimp. rewrite arrowcons. apply IHs2. auto. rewrite minus_arrow ; auto.
Qed.

Hint Resolve wf_subst_arrowend.

(** * Lemmas *)

(** ** Termination Proof Lemmas *)

Lemma arrow_lt_size_t : forall l l' r r', size_t (l, l') + size_t (r, r') < size_t (arrow l r, arrow l' r').
Proof.
  intros ; mysimp ; try omega.
Qed.

Lemma non_member_remove_length : forall C v, ~ member C v -> length (remove v C) = length C.
Proof.
  induction C ; auto ; mysimp ; intros ; mysimp ; try tauto.
Qed.

Lemma remove_varctxt_length : forall C v, member C v -> length (remove v C) < length C.
Proof.
  intros ; induction C ; simpl in * ; try contradiction ; mysimp ;
  destruct (member_dec C v) ; auto with arith ;
   match goal with
     | [H : ~ member _ _ |- _] => rewrite (non_member_remove_length _ _ H) ; auto with arith
   end.
Qed.

Hint Resolve remove_varctxt_length.

(** ** Relating occurs check and well formedness of types *)

Lemma occurs_wf_ty v C t : wf_ty C t -> ~ occurs v t -> wf_ty (remove v C) t.
Proof.
  induction t ; mysimp ; try tauto.
Qed.

Hint Resolve occurs_wf_ty.

(** ** Some Obvious Facts About Arrowlications *)

Lemma arrow_subst_eq : forall l l' r r' s,  apply_subst s l = apply_subst s l' ->
                                          apply_subst s r = apply_subst s r' ->
                                          apply_subst s (arrow l r) = apply_subst s (arrow l' r').
Proof.
  intros ; do 2 rewrite apply_subst_arrow ; fequals*.
Qed.

Hint Resolve arrow_subst_eq.

(** ** Extensionality Lemmas For Substitutions *)

Lemma ext_subst_var_ty : forall s s', (forall v, apply_subst s (var v) = apply_subst s' (var v)) ->
                                       forall t, apply_subst s t = apply_subst s' t.
Proof.
  intros ; induction t ; mysimp ; try (do 2 rewrite apply_subst_arrow) ;
     simpl in * ; auto ; try (do 2 rewrite apply_subst_con) ; auto.
    try (rewrite IHt1 ; auto). try (rewrite IHt2 ; auto).
Qed.

(*
Lemma ext_subst_ty_var : forall s s', (forall t, apply_subst s t = apply_subst s' t) ->
                                      forall v, apply_subst s (var v) = apply_subst s' (var v).
Proof.
  mysimp.
Qed.


Hint Resolve ext_subst_var_ty ext_subst_ty_var.
*)

Lemma subst_occurs : forall t v u, ~ occurs v u -> u = apply_subst ((v, t)::nil) u.
Proof.
  induction u ; mysimp ; intros ; try firstorder ; try congruence.
Qed.

Hint Resolve subst_occurs.

(** * Specification of the Unification Algorithm *)

Inductive UnifyFailure : ty -> ty -> Prop :=
  | occ_fail  : forall v t, occurs v t -> UnifyFailure (var v) t
  | occ_fail'  : forall v t, occurs v t -> UnifyFailure t (var v)
  | diff_cons : forall n n', n <> n' -> UnifyFailure (con n) (con n')
  | con_arrow   : forall n l r, UnifyFailure (con n) (arrow l r)
  | arrow_con   : forall n l r, UnifyFailure (arrow l r) (con n)
  | arrow_left  : forall l l' r r', UnifyFailure l l' -> UnifyFailure (arrow l r) (arrow l' r')
  | arrow_right  : forall l l' r r', UnifyFailure r r' -> UnifyFailure (arrow l r) (arrow l' r') .

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

Definition wf_constraints (c : constraints) :=
  wf_tys (get_ctxt c) (fst (get_tys c)) (snd (get_tys c)).

(*
Lemma wf_constr_list_remove : forall l C v t, wf_constr_list C l ->
                                                member C v ->
                                                ~ occurs v t ->
                                                wf_ty C t ->
                                                wf_constr_list (remove v C) (apply_subst_constraint ((v,t) :: nil) l).
Proof.
  induction l ; intros ; mysimp ; destruct a ; simpl in * ; mysimp.
Defined.

Hint Resolve wf_constr_list_remove.
*)


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
             forall s', unifier (fst (get_tys c)) (snd (get_tys c)) s' ->
               exists s'', forall v, apply_subst s' (var v) = apply_subst (compose_subst s s'') (var v)})
           + { UnifyFailure (fst (get_tys c)) (snd (get_tys c)) }.

(** * Main definition of the unification function *)

(* The unification algorithm is defined by a combinator that performs well-founded recursion
   over a well-founded relation. The constraints_lt is a well founded relation over constraints,
   so, we can use the library combinator for well-founded recursion in order to compute the
   unifier over such constraints.

   The algorithm below uses a lot of type annotations, needed to pattern-match over dependent
   types.

   Also, the algorithm definition is polluted by tactics. This is necessary in order to
   generate the proof terms to the obligations to ensure the well-foundness of the recursive
   calls and to finish the proofs for soundness and completness of the algorithm.*)


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

Lemma arrow_lt_constraints: forall l l1 l2 r1 r2,
    constraints_lt (mk_constraints l l1 l2) (mk_constraints l (arrow l1 r1) (arrow l2 r2)).
Proof.
  intros ; apply right_lex ; auto.
  simpl.
  omega.
Defined.

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
                                 match unify' (mk_constraints _ (apply_subst s1 r1) (apply_subst s1 r2)) _ with
                                 | inright E => inright _
                                 | inleft _ (exist _ s2 HS') => inleft _ (@exist substitution _ (compose_subst s1 s2) _)
                                 end
                               end
  | _ => inright _
  end.
Next Obligation.
splits; mysimp.
unfold unifier. reflexivity.
intros.
exists s'.
rewrite compose_subst_nil1.
intros. reflexivity.
Defined.
Next Obligation.
splits; mysimp.
unfold unifier. mysimp.
intros.
unfold wf_constraints in wfl.
rewrite <- Heq_anonymous0 in wfl.
simpl in wfl.
destruct wfl.
apply wf_ty_var in H0.
assumption.
unfold wf_constraints in wfl.
rewrite <- Heq_anonymous0 in wfl.
simpl in wfl.
destruct wfl.
Admitted.
Next Obligation.
  intros; splits; intros; mysimp.
  reflexivity.
  exists s'.
  rewrite compose_subst_nil1.
  intros. reflexivity.
Defined.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
unfold wf_constraints in wfl.
rewrite <- Heq_anonymous in wfl.
simpl in wfl.
destruct wfl.
destruct H.
destruct H0.
erewrite constraints_mk_inversion with (C := get_ctxt l).
repeat rewrite <- Heq_anonymous.
simpl.
eapply arrow_lt_constraints.
symmetry. apply Heq_anonymous.
reflexivity.
Defined.
Next Obligation.
unfold wf_constraints in *.
rewrite <- Heq_anonymous in wfl.
simpl in *.
destruct wfl.
split.
Admitted.
Next Obligation.
econstructor.
Defined.
Next Obligation.
  simpl.
Admitted.
Next Obligation.
  simpl.
  unfold wf_constraints in *.
  clear Heq_anonymous.
  repeat rewrite <- Heq_anonymous0 in wfl.
  simpl in wfl.
  destruct wfl.
  simpl.
  splits.
Admitted.
Next Obligation.
  econstructor.
  simpl in *.
Admitted.
Next Obligation.
  splits; simpl.
Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  intros; splits; intros;
  intuition; inversion H2.
Defined.
Next Obligation.
  intros; splits; intros;
  intuition; inversion H3.
Defined.
Next Obligation.
  apply well_founded_constraints_lt.
Defined.
          

Definition unify_body (l : constraints)
                      (unify : forall (l'  : constraints), constraints_lt l' l -> unify_type l') : unify_type l.
intros.

Definition unify_body (l : constraints)
                      (unify : forall (l'  : constraints),
                                 constraints_lt l' l -> unify_type l') : unify_type l.
   unfold unify_type ; intros prf ;
   destruct l as [C l] ; simpl ;
   refine (
       match l as l' return l = l' ->
          ({ s | unifier l s /\ wf_subst C s /\
              forall s', unifier l s' ->
              exists s'', forall v, apply_subst s' (var v) = apply_subst (s ++ s'') (var v)} +
                        { UnifyFailure l }) with
          | nil => fun H1 => inleft _ (@exist substitution _ nil _)
          | (t,t') :: l' => fun H1 =>
              match eq_ty_dec t t' return
                 ({ s | unifier l s /\ wf_subst C s /\
                forall s', unifier l s' ->
                 exists s'', forall v, apply_subst s' (var v) = apply_subst (s ++ s'') (var v)})
                    + {UnifyFailure l} with
                | left _ =>
                       match unify (mk_constraints C l') _ _ with
                        | inleft (exist _ s _) =>  inleft _ (@exist substitution _ s _)
                        | inright _ => inright _ _
                      end
                | right _ =>
                    match t as t1, t' as t1'
                       return t = t1 -> t' = t1' ->
                         ({ s | unifier l s /\ wf_subst C s /\
                           forall s', unifier l s' ->
                exists s'', forall v, apply_subst s' (var v) = apply_subst (s ++ s'') (var v)})
                                    + { UnifyFailure l } with
                        | var v, t =>
                            fun H1 H2 =>
                              match occurs_dec v t with
                                | left _ => inright _ _
                                | right _ =>
                                    match unify (mk_constraints (minus C (v :: nil))
                                                (apply_subst_constraint ((v,t) :: nil) l')) _ _ with
                                      | inleft (exist _ s _) => inleft _ (@exist substitution _ ((v,t) :: s) _ )
                                      | inright _ => inright _ _
                                    end
                              end
                        | t, var v =>
                            fun H1 H2 =>
                              match occurs_dec v t with
                                | left _ => inright _ _
                                | right _ =>
                                    match unify (mk_constraints (minus C (v :: nil))
                                                (apply_subst_constraint ((v,t) :: nil) l')) _ _ with
                                      | inleft (exist _ s _) => inleft _ (@exist substitution _ ((v,t) :: s) _ )
                                      | inright _ => inright _ _
                                    end
                              end
                        | con n, con n' =>
                            fun H1 H2 => inright _ _
                        | con _ , arrow _ _ =>
                            fun H1 H2 => inright _ _
                        | arrow _ _, con _ =>
                            fun H1 H2 => inright _ _
                        | arrow l1 r, arrow l1' r' =>
                            fun H1 H2 =>
                              match unify (mk_constraints C ((l1,l1') :: (r,r') :: l')) _ _ with
                                | inleft (exist _ s _)  => inleft _ (@exist substitution _ s _)
                                | inright _ => inright _ _
                              end
                    end (refl_equal t) (refl_equal t')
              end
       end (refl_equal l)
     ) ; clear unify ;  unfolds in prf ; simpl in * ; substs ; mysimp ; eauto ; simpl in * ; intros ;
        try (do 2 fequals* ; symmetry ; auto ; fail) ; mysimp ; unfold wf_constraints in * ; simpl in * ; mysimp ;
        try (match goal with
             | [H : apply_subst ?s (arrow _ _) = apply_subst ?s (arrow _ _),
                Hu : unifier _ ?s,
                H1 :  forall s',
                        apply_subst s' _ = apply_subst s' _ /\
                        apply_subst s' _ = apply_subst s' _ /\ unifier _ s' ->
                        exists s'',
                          forall v : id, _ |- _ ] =>
                   do 2 rewrite apply_subst_arrow in H ; injection H ; clear H ;
                   intros Ha Hb ; destruct (H1 _ (conj Hb (conj Ha Hu))) as [sc Hc] ;
                   exists* sc 
               | [H : apply_subst ?s (var _) = apply_subst ?s ?t,
                  Hu : unifier _ ?s,
                  H1 : forall s', unifier _ s' -> _ |- _] =>
                      apply (unifier_subst _ _ _ _ H) in Hu ; destruct (H1 _ H4) as [sa Ha] ;
                      eexists ; intros ; case_if* ; substs ; try rewrite H ;
                      eapply ext_subst_var_ty in Ha ; eauto
               | [H : apply_subst ?s ?t = apply_subst ?s (var _),
                  Hu : unifier _ ?s,
                  H1 : forall s', unifier _ s' -> _ |- _] =>
                       symmetry in H ; apply (unifier_subst _ _ _ _ H) in Hu ;
                       destruct (H1 _ Hu) as [sa Ha] ; eexists ; intros ; case_if* ; substs ;
                       try rewrite H ; eapply ext_subst_var_ty in Ha ; eauto
             end) ; try (apply wf_constr_list_remove ; auto ; splits*).
                         apply f_equal. info_auto.
                         apply wf_constr_list_remove ; auto.
                         mysimp.
                         apply f_equal.
                         rewrite sub_arrow_dist.
                         symmetry.
                         eapply subst_occurs.
                         intro.
                         intuition.

Defined.

Definition unify : forall l : constraints, unify_type l :=
  well_founded_induction well_founded_constraints_lt unify_type unify_body.

Print Opaque Dependencies unify.

Definition projSubs (A : Type) (B : Prop)
           (P : A -> Prop) (u : sumor (sig P) B) : option A :=
  match u with
  | inleft _ (exist _ v _) => Some v
  | inright _ => None
  end.
Definition ex_wf := wf_constr_list ((1)::(2)::nil) ((var 1, var 2)::nil).

Check (unify (existT _ (0::1::nil) ((var 1, var 0)::nil)) _).


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
  end);
  mysimp.
  apply wf_ty_app.
  auto.
  apply wf_ty_app_comm.
  apply wf_ty_app.
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

Definition unify_simple : forall t1 t2 : ty, option substitution.
  intros.
  pose proof ids_ty_dep2 as dep.
  specialize dep with (tau:=t1) (tau':=t2).
  destruct dep.
  refine ((projSubs ((unify (existT _ (x) ((t1, t2)::nil))) _))).
  unfold wf_constraints.
  simpl.
  intuition.
Defined.

Check (fun t1 t2 x => (unify (existT _ (x) ((t1, t2)::nil)))).


Definition unify_simple_dep : forall t1 t2 : ty, 
{x & {s : substitution | unifier (get_list_constr (existT (fun _ : list id => list (ty * ty)) x
((t1, t2) :: nil))) s /\ wf_subst (get_ctxt (existT (fun _ : list id => list (ty * ty)) x ((t1, t2) :: nil))) s /\
  (forall s' : substitution, unifier (get_list_constr
        (existT (fun _ : list id => list (ty * ty)) x
           ((t1, t2) :: nil))) s' -> exists s'' : list (id * ty), forall v : id, apply_subst s' (var v) = apply_subst (s ++ s'') (var v))} +
  {UnifyFailure (get_list_constr (existT (fun _ : list id => list (ty * ty)) x ((t1, t2) :: nil)))} }.
Proof.
  intros.
  pose proof ids_ty_dep2 as dep.
  specialize dep with (tau:=t1) (tau':=t2).
  destruct dep.
  exists x.
  refine ((((unify (existT _ _ ((t1, t2)::nil))) _))).
  unfold wf_constraints.
  simpl.
  intuition.
Qed.

Check unify_simple_dep.

Definition FV_subst (s: substitution) := ((dom s) ++ (img_ids s)).


Fixpoint id_in_subst (i : id) (s : substitution) : option ty :=
  match s with
    | nil => None
    | (i', tau)::s' => if eq_id_dec i i' then Some tau else id_in_subst i s'
  end.