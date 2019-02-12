Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.

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

(** * Definition of Constraints **)

(** A constraint is just a pair of types *)

Definition constr := (ty * ty)%type.

(** A constraint list is just a list of pairs *)

Definition list_constr := list constr.

(** Measures of constraints follows direct from the type size definition *)

Definition constr_size (c : constr) : nat :=
  match c with
    (t,t') => size t + size t'
  end.

Fixpoint list_measure (l : list_constr) : nat :=
  match l with
    | nil => 0
    | p :: l => constr_size p + list_measure l
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

Fixpoint wf_constr_list (C : varctxt) (l : list_constr)  : Prop :=
  match l with
    | nil => True
    | (t,t') :: C' => wf_ty C t /\ wf_ty C t' /\ wf_constr_list C C'
  end.

(** * The "Real" Constraint definition *)

 (** We define a constraint as a dependent product of
    a variable context and a list of constraints.
    This is needed for a simple termination argument
    for the unification algorithm. **)

Definition constraints := sigT (fun _ : varctxt => list_constr).

Definition get_ctxt(c : constraints) : varctxt := let (v,_) := c in v.
Definition get_list_constr(c : constraints) : list_constr := let (_,l) := c in l.
Definition mk_constraints(C : varctxt)(l : list_constr) : constraints := existT _ C l.

(** ** Constraint ordering *)

(** A strict order on constraints. Here we use the library definition of lexicographic orderings. *)

Definition constraints_lt : constraints -> constraints -> Prop :=
  lexprod varctxt (fun _ => list_constr)
          (fun (x y : varctxt) => length x < length y)
          (fun (x : varctxt) (l l' : list_constr) => list_measure l < list_measure l').

(** A proof that the order is well-founded *)

Definition well_founded_constraints_lt : well_founded constraints_lt :=
  @wf_lexprod varctxt (fun _ : varctxt => list_constr)
              (fun (x y : varctxt) => length x < length y)
              (fun (x : varctxt) (l l' : list_constr) => list_measure l < list_measure l')
              (well_founded_ltof varctxt (@length id))
              (fun _ => well_founded_ltof list_constr list_measure).

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

Fixpoint sub (t1 : ty) (x : id) (t2 : ty) : ty :=
  match t2 with
    | var n => if eq_id_dec x n then t1 else var n
    | con n => con n
    | arrow l r => arrow (sub t1 x l) (sub t1 x r)
  end.

Lemma sub_arrow_dist : forall t v t0 t1, arrow (sub t v t0) (sub t v t1) = sub t v (arrow t0 t1).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

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
                                               wf_ty (remove x ctx) (sub u x t).
Proof.
  induction t ; simpl ; intros ; mysimp.
Qed.

(* begin hide *)

Hint Resolve subst_remove.

(* end hide *)

(** ** Substitution Definitions and Its Well Formedness Predicate *)

(** Substitution and its dom *)

Definition substitution := list (id * ty).

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

(** Substitution arrowlication functions *)

Fixpoint apply_subst (s : substitution) (t : ty) : ty :=
  match s with
    | nil => t
    | (v,t') :: s' => apply_subst s' (sub t' v t)
  end.

Fixpoint apply_subst_constraint (s : substitution) (l : list_constr) : list_constr :=
  match l with
    | nil => nil
    | (t,t1) :: l' => (apply_subst s t , apply_subst s t1) :: apply_subst_constraint s l'
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

(** If s is a well-formed substitution with respect to C,
   and t is a well-formed type with respect to C, s t is
   a well-formed type with respect to C - (dom s) *)

Lemma substs_remove : forall s C t , wf_subst C s ->
                                     wf_ty C t ->
                                     wf_ty (minus C (dom s)) (apply_subst s t).
Proof.
  induction s ; mysimp ; intros ; mysimp.
  generalize (IHs (remove a C)) ; rewrite minus_remove ; intros ; auto.
Qed.

Hint Resolve substs_remove.

Lemma minus_arrow : forall (C : varctxt) s v t, minus C (dom (s ++ (v,t) :: nil)) = remove v (minus C (dom s)).
Proof.
  induction s ; mysimp ; intros ; mysimp ; rewrite IHs ; auto.
Qed.

(** ** Some Obvious Facts About Substitutions **)

Lemma apply_subst_id : forall t, apply_subst nil t = t.
Proof.
  induction t ; mysimp.
Qed.

Lemma apply_subst_con : forall s n, apply_subst s (con n) = con n.
Proof.
  induction s ; mysimp.
Qed.

Lemma apply_subst_arrow : forall s l r, apply_subst s (arrow l r) = arrow (apply_subst s l) (apply_subst s r).
Proof.
  induction s ; mysimp.
Qed.

Lemma apply_subst_end : forall s v t t', apply_subst (s ++ (v,t) :: nil) t' = sub t v (apply_subst s t').
Proof.
  induction s ; mysimp.
Qed.

Lemma apply_subst_append : forall s2 s1 t, apply_subst (s1 ++ s2) t = apply_subst s2 (apply_subst s1 t).
Proof.
  induction s2 ; intros ; simpl. rewrite <- app_nil_end ; auto.
  assert (s1 ++ a :: s2 = (s1 ++ (a::nil)) ++ s2).
  rewrite app_ass ; auto. rewrite H. destruct a. rewrite (IHs2 (s1 ++ (i,t0)::nil)).
  rewrite <- apply_subst_end. auto.
Qed.

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

Lemma lt_list_constr_lt_measure : forall t t' l, list_measure l < list_measure ((t,t') :: l).
Proof.
  induction t ; destruct t' ; intros ; simpl in * ; mysimp.
Qed.

Hint Resolve lt_list_constr_lt_measure.

Lemma lt_list_constr_lt_constraints : forall t t' C l, constraints_lt (mk_constraints C l) (mk_constraints C ((t,t') :: l)).
Proof.
  intros ; apply right_lex ; auto.
Qed.

Lemma arrow_lt_measure : forall l l' r r' lc, list_measure ((l,l') :: (r, r') :: lc) < list_measure ((arrow l r, arrow l' r') :: lc).
Proof.
  intros ; induction lc ; mysimp ; try omega.
Qed.

Lemma arrow_lt_constraints : forall l l' r r' lc C, constraints_lt (mk_constraints C ((l,l') :: (r,r') :: lc))
                                                                 (mk_constraints C ((arrow l r, arrow l' r') :: lc)).
Proof.
  intros ; apply right_lex ; mysimp ; try omega.
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

Lemma varctxt_lt_constraints_varl :
  forall C v t l, member C v ->
                  constraints_lt (mk_constraints (remove v C) (apply_subst_constraint ((v,t) :: nil) l))
                                 (mk_constraints C ((var v, t) :: l)).
Proof.
  intros ; apply left_lex ; auto.
Defined.

Lemma varctxt_lt_constraints_varr :
  forall C v t l, member C v ->
                  constraints_lt (mk_constraints (remove v C) (apply_subst_constraint ((v,t) :: nil) l))
                                 (mk_constraints C ((t, var v) :: l)).
Proof.
  intros ; apply left_lex ; auto.
Defined.

Hint Resolve lt_list_constr_lt_constraints arrow_lt_constraints
             varctxt_lt_constraints_varl varctxt_lt_constraints_varr.

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

Lemma ext_subst_ty_var : forall s s', (forall t, apply_subst s t = apply_subst s' t) ->
                                      forall v, apply_subst s (var v) = apply_subst s' (var v).
Proof.
  mysimp.
Qed.


Hint Resolve ext_subst_var_ty ext_subst_ty_var.

Lemma sub_occurs : forall t v u, ~ occurs v u -> u = sub t v u.
Proof.
  induction u ; mysimp ; intros ; try firstorder ; try congruence.
Qed.

Hint Resolve sub_occurs.

(** * Specification of the Unification Algorithm *)

Inductive UnifyFailure : list_constr -> Prop :=
  | occ_fail  : forall v t lc, occurs v t -> UnifyFailure (((var v), t) :: lc)
  | occ_fail'  : forall v t lc, occurs v t -> UnifyFailure ((t, (var v)) :: lc)
  | diff_cons : forall n n' lc, n <> n' -> UnifyFailure (((con n),(con n')) :: lc)
  | con_arrow   : forall n l r lc, UnifyFailure (((con n),(arrow l r)) :: lc)
  | arrow_con   : forall n l r lc, UnifyFailure (((arrow l r), (con n)) :: lc)
  | arrow_left  : forall l l' r r' lc, UnifyFailure ((l,l') :: lc) -> UnifyFailure (((arrow l r), (arrow l' r')) :: lc)
  | arrow_right  : forall l l' r r' lc, UnifyFailure ((l,l') :: (r, r') :: lc) -> UnifyFailure (((arrow l r), (arrow l' r')) :: lc)
  | constr_rec : forall t t' l, UnifyFailure l -> UnifyFailure ((t,t') :: l)
  | subs_rec : forall t t' s l, UnifyFailure (apply_subst_constraint s l) -> UnifyFailure ((t,t') :: l).

Hint Constructors UnifyFailure.

(** ** Definition of a unifier for a list of constraints *)

Fixpoint unifier (cs : list_constr) (s : substitution) : Prop :=
  match cs with
    | nil => True
    | (t,t') :: cs' => apply_subst s t = apply_subst s t' /\ unifier  cs' s
  end.

(** a simple lemma about unifiers and variable substitutions *)

Lemma unifier_arrowend : forall l v t s,
                         unifier (apply_subst_constraint ((v, t) :: nil) l) s ->
                         unifier l ((v,t) :: s).
Proof.
  induction l ; intros ; mysimp ;
    try (match goal with
          | [a : constr |- _] => destruct a
         end) ; simpl in * ; try splits*.
Defined.

Lemma unify_ty : forall t v t' s, apply_subst s (var v) = apply_subst s t' ->
                                  apply_subst s t = apply_subst s (sub t' v t).
Proof.
  induction t ; intros ; mysimp.
Defined.

Hint Resolve unify_ty.

Lemma unifier_subst : forall l v t s, apply_subst s (var v) = apply_subst s t ->
                                        unifier l s ->
                                        unifier (apply_subst_constraint ((v,t) :: nil) l) s.
Proof.
  induction l ; intros ; mysimp ;
    try (match goal with
          | [a : constr |- _] => destruct a
         end) ; simpl in * ; mysimp.
  assert (apply_subst s (var v) = apply_subst s t) ; auto.
  apply unify_ty with (t := t0) in H.
  apply unify_ty with (t := t1) in H2.
  rewrite <- H. rewrite <- H2. auto.
Defined.

Hint Resolve unifier_arrowend unifier_subst.

Definition wf_constraints (c : constraints) :=
  wf_constr_list (get_ctxt c) (get_list_constr c).

Lemma wf_constr_list_remove : forall l C v t, wf_constr_list C l ->
                                                member C v ->
                                                ~ occurs v t ->
                                                wf_ty C t ->
                                                wf_constr_list (remove v C) (apply_subst_constraint ((v,t) :: nil) l).
Proof.
  induction l ; intros ; mysimp ; destruct a ; simpl in * ; mysimp.
Defined.

Hint Resolve wf_constr_list_remove.


(** * Type of the unification algorithm *)

(*
The type of unification algorithm specifies that from a list of well-formed constraints
we can either:

1 - Produce a well-formed substitution s such that it unifies the constraints and s is the
    least of such unifiers.
2 - It returns a proof that no such unifier exists.

*)

Definition unify_type (c : constraints) := wf_constraints c ->
           ({ s | unifier (get_list_constr c) s /\ wf_subst (get_ctxt c) s /\
             forall s', unifier (get_list_constr c) s' ->
               exists s'', forall v, apply_subst s' (var v) = apply_subst (s ++ s'') (var v)})
           + { UnifyFailure (get_list_constr c) }.

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
                         eapply sub_occurs.
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
