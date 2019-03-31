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
  induction c; crush.
Qed.

Hint Resolve member_app.

Lemma member_app2 : forall c c' i, member c' i -> member (c++c') i.
Proof.
  induction c; crush.
Qed.

Hint Resolve member_app2.

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
  induction c; crush.
Qed.

Hint Resolve member_app_or.

Lemma member_or_app : forall c c' i, member c i \/ member c' i <-> member (c++c') i.
Proof.
  split; crush.
Qed.

Hint Resolve member_or_app.

Lemma member_app_comm : forall c c' i, member (c'++c) i -> member (c++c') i.
Proof.
  intros.
  apply member_or_app in H; crush.
Qed.

Hint Resolve member_app_comm.

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
  induction t; crush.
Qed.

Hint Resolve wf_ty_cons.

Lemma wf_ty_app : forall c' c t, wf_ty c t -> wf_ty (c++c') t.
Proof.
  induction c; induction t; crush.
Qed.

Hint Resolve wf_ty_app.
      
Lemma wf_ty_app_comm : forall c c' t, wf_ty (c++c') t -> wf_ty (c'++c) t.
Proof.
  induction c'; crush.
  induction t; crush.
  apply member_app_comm in H.
  crush.
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

(** Removing a variable from a variable context *)

Fixpoint remove (v : id) (ctx : varctxt) : varctxt :=
  match ctx with
    | nil => nil
    | y :: ys => if eq_id_dec y v then remove v ys else y :: (remove v ys)
  end.

Lemma remove_nil : forall i, remove i [] = [].
Proof.
  crush.
Qed.

Hint Resolve remove_nil.
Hint Rewrite remove_nil.

(** Suppose that a type t is well formed with respect to a variable context ctx and
    the variable x is free in t,
    if we substitute x for u and u is well formed with respecto to ctx - {x},
    we get a type that is well formed with respect to ctx - {x}.
    This is formalized by the lemma subst_remove. *)

Lemma subst_remove' : forall x t ctx, member ctx t -> x <> t -> member (remove x ctx) t.
Proof.
  induction ctx ; crush.
Qed.

Hint Resolve subst_remove'.

Lemma subst_remove : forall t x ctx, wf_ty ctx t -> member ctx x ->
                                     forall u, wf_ty (remove x ctx) u ->
                                               wf_ty (remove x ctx) (apply_subst ((x, u)::nil) t).
Proof.
  induction t ; crush.
Qed.

Hint Resolve subst_remove.

(** Removing a list of names from a given variable context. *)

Fixpoint minus (C : varctxt) (xs : list id) : varctxt :=
  match xs with
    | nil => C
    | x :: xs => remove x (minus C xs)
  end.

Lemma minus_nil1 : forall l, minus nil l = nil.
Proof.
  intros.
  induction l; mysimp.
  rewrite IHl. reflexivity.
Qed.
    
Hint Resolve minus_nil1.
Hint Rewrite minus_nil1:RE.

Lemma minus_nil2 : forall l, minus l nil = l.
Proof.
  intros.
  reflexivity.
Qed.

Hint Resolve minus_nil2.
Hint Rewrite minus_nil2:RE.

(** Definition of a  well formed substitution. A substitution is well formed,
    if form each pair (v,t), where v is a variable and t a type, we have that
    v is in a variable context C and t is well formed in the variable context
    C - {v}. *)

Fixpoint wf_subst (C : varctxt) (s : substitution) : Prop :=
  match s with
    | nil => True
    | (v,t) :: s' => member C v /\ wf_ty (remove v C) t /\ wf_ty (minus C (dom s')) t /\ (wf_subst (remove v C) s') 
  end.

Lemma remove_comm : forall x y C, remove x (remove y C) = remove y (remove x C).
Proof.
  induction C ; crush.
Qed.

Hint Resolve remove_comm.
Hint Rewrite remove_comm:RELOOP.

Lemma minus_remove : forall C2 C1 x, minus (remove x C1) C2 = remove x (minus C1 C2).
Proof.
  induction C2; crush.
Qed.

Hint Resolve minus_remove.
Hint Rewrite minus_remove:RE.

Lemma minus_arrow : forall (C : varctxt) s v t, minus C (dom (s ++ (v,t) :: nil)) = remove v (minus C (dom s)).
Proof.
  induction s ; crush. 
Qed.

Hint Resolve minus_arrow.
Hint Rewrite minus_arrow:RE.

Lemma member_remove_false : forall i C, member (remove i C) i -> False.
Proof.
  induction C; crush.
Qed.

Hint Resolve member_remove_false.

Lemma wf_ty_var : forall i C, member C i <-> wf_ty C (var i).
Proof.
  split;
  induction C; crush.
Qed.

Hint Resolve wf_ty_var.

Lemma wf_ty_var_false : forall i C, wf_ty (remove i C) (var i) -> False.
Proof.
  induction C; crush.
Qed.
  
Lemma subst_remove_single : forall a C t t0, wf_ty (remove a C) t -> wf_ty C t -> wf_ty C t0 ->
                                     wf_ty (remove a C) (apply_subst ((a, t0)::nil) t).
Proof.
  induction t; crush.
  apply member_remove_false in H. contradiction.
Qed.

Hint Resolve subst_remove_single.

Lemma member_diff_inversion : forall a i0 C, a <> i0 -> member (a :: C) i0 -> member C i0.
Proof.
  crush.
Qed.

Hint Resolve member_diff_inversion.

Lemma wf_ty_cons_inversion : forall t i C, wf_ty C t -> wf_ty (i::C) t.
Proof.
  crush.
Qed. 

Hint Resolve wf_ty_cons_inversion.

Lemma member_remove_inversion : forall i i0 C, member (remove i C) i0 -> member C i0.
Proof.
  induction C;
  crush.
Qed.

Hint Resolve member_diff_inversion member_remove_inversion.

Lemma wf_ty_remove_inversion : forall i C t, wf_ty (remove i C) t -> wf_ty C t.
Proof.
  induction t; crush.
Qed.

Hint Resolve wf_ty_remove_inversion.

Lemma member_remove_remove_comm : forall C i j k, member (remove i (remove j C)) k -> member (remove j (remove i C)) k.
Proof.
  induction C; crush.
Qed.

Hint Resolve member_remove_remove_comm.

Lemma member_minus_remove : forall a C i0 i, member (minus (remove i0 C) a) i -> member (remove i0 (minus C a)) i.
Proof.
  induction a; crush.
Qed.

Hint Resolve member_minus_remove.

Lemma wf_ty_remove_remove_comm : forall i j C t, wf_ty (remove i (remove j C)) t -> wf_ty (remove j (remove i C)) t.
Proof.
  induction t; crush.
Qed.

Hint Resolve wf_ty_remove_remove_comm.

Lemma wf_subst_remove_inversion : forall s i C, wf_subst (remove i C) s -> wf_subst C s.
Proof.
  induction s; crush.
  rewrite remove_comm in H2.
  eauto.
Qed.

Hint Resolve wf_subst_remove_inversion.

Lemma compose_subst_nil_r : forall s, compose_subst s nil = s.
Proof.
  induction s; crush.
Qed.

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
Hint Rewrite subst_occurs:RE.

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
                           (forall st, (new_tv_ty (fst (get_tys c)) st /\ new_tv_ty (snd (get_tys c)) st) -> new_tv_subst s st) /\
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

Definition ids_eliminated (s : substitution) (t1 : ty) : list id := (minus (ids_ty t1) (ids_ty (apply_subst s t1))).

Lemma arrowcons (A:Type) : forall (s1 s2:list A) x, s1 ++ x::s2 = (s1 ++ x::nil) ++ s2.
  intros ; rewrite app_ass ; auto.
Qed.

Lemma  minus_app_comm_cons : forall l1 l2 l a, minus l (l1 ++ a::l2) = minus l (a::l1 ++ l2).
Proof. 
  induction l1; intros. reflexivity.
  simpl.
  rewrite remove_comm.
  fequals.
  rewrite IHl1.
  simpl. reflexivity.
Qed.

Lemma  minus_app_comm : forall l1 l2 l, minus l (l1 ++ l2) = minus l (l2 ++ l1).
Proof.
  induction l1. intros. simpl. rewrite app_nil_r. reflexivity.
  intros.
  rewrite minus_app_comm_cons. simpl.
  rewrite IHl1. reflexivity.
Qed.

Lemma ids_ty_apply_subst : forall s t, (ids_ty (apply_subst s t)) = List.concat (List.map ids_ty ( (List.map (apply_subst s) (List.map var (ids_ty t))))).
Proof.
  intros.
  induction t; mysimp.
  rewrite app_nil_r. reflexivity.
  repeat rewrite map_app.
  repeat rewrite concat_app.
  rewrite <- IHt1.
  rewrite <- IHt2.
  reflexivity.
Qed.

Fixpoint member_b (C : varctxt) (i : id) : bool :=
  match C with
    | nil => false
    | v :: vs => if eq_id_dec v i then true else member_b vs i
  end.

Fixpoint wf_ty_b (C : varctxt) (t : ty) : bool :=
  match t with
    | var v => member_b C v
    | con _ => true
    | arrow l r => andb (wf_ty_b C l) (wf_ty_b C r)
  end.

Fixpoint in_list (l : list id) (i : id) :=
  match l with
  | nil => true
  | j::l' => if eq_id_dec j i then true else in_list l' i
  end.

Lemma minus_dist_r : forall l l1 l2, (minus l (l1 ++ l2) = minus (minus l l1) l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl.
    rewrite IHl1.
    rewrite minus_remove.
    reflexivity.
Qed.

Lemma not_in_t : forall i C t, wf_ty (remove i C) t -> minus [i] (ids_ty t) = [i].
Proof.
  intros.
  induction t; mysimp.
  apply wf_ty_var_false in H.
  contradiction.
  destruct H.
  apply IHt1 in H.
  apply IHt2 in H0.
  rewrite minus_dist_r.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma remove_remove_inversion : forall a i, remove i (remove i a) = (remove i a).
Proof.
  intros.
  induction a.
  reflexivity.
  simpl.
  destruct (eq_id_dec a i).
  assumption.
  simpl.
  destruct (eq_id_dec a i); intuition.
  rewrite IHa.
  reflexivity.
Qed.

Lemma minus_remove_dist1 : forall i a b, remove i (minus a b) = minus (remove i a) (remove i b).
Proof.
  intros.
  induction b.
  - reflexivity.
  - simpl in *.
    destruct (eq_id_dec a0 i).
    subst.
    rewrite <- IHb.
    rewrite remove_remove_inversion.
    reflexivity.
    simpl in *.
    rewrite remove_comm.
    fequals.
Defined.

Lemma minus_remove_dist2 : forall i a b, remove i (minus a b) = minus (remove i a) b.
Proof.
  intros.
  induction b.
  - reflexivity.
  - simpl in *.
    rewrite <- IHb.
    rewrite remove_comm.
    reflexivity.
Defined.

Lemma apply_not_chance_not_occurs : forall a t0 s t, ~ occurs a t0 -> apply_subst ((a, t0) :: s) t = t -> ~ occurs a t.
  intros.
  intro.
  induction t.
  simpl in H0.
  destruct (eq_id_dec i a); intuition.
  subst.
  simpl in *. destruct (eq_id_dec a a); intuition.
  subst.
  simpl in *. destruct (eq_id_dec a a); intuition.
  simpl in *. destruct (eq_id_dec a i); intuition.
  simpl in *. destruct (eq_id_dec i a); intuition.
  simpl in H1. contradiction.
  rewrite apply_subst_arrow in H0.
  inversion H0.
  auto.
  simpl in H1.
  destruct H1.
  auto.
  auto.
Qed.  

Lemma substs_remove_var' : forall s C i, wf_subst C s ->
                                     wf_ty C (var i) ->
                                     wf_ty C  (apply_subst s (var i)).
Proof.
  induction s . intros ; simpl in *; mysimp.
  intros.
  destruct a.
  specialize IHs with (i := i).
  simpl in H.
  destructs H.
  simpl.
  destruct (eq_id_dec i0 i).
  - subst.
    eauto.
  -
  specialize IHs with (C := (C)).
  simpl in *.
  cases (find_subst s i);
   eauto.
Qed. 

Lemma substs_remove' : forall t s C , wf_subst C s ->
                                     wf_ty C t ->
                                     wf_ty C (apply_subst s t).
Proof.
  induction t; intros; mysimp.
  rewrite apply_subst_fold.
  apply substs_remove_var'; auto.
  destruct H0.
  auto.
  destruct H0.
  auto.
Qed.

Lemma wf_ty_remove_minus_inversion : forall s a C t, wf_ty (remove a (minus C (dom s))) t -> wf_ty (remove a C) t.
Proof.
  induction s; intros; mysimp; simpl in *; eauto.
Qed.

Lemma wf_subst_remove_comm : forall s C b a, wf_subst (remove a (remove b C)) s -> wf_subst (remove b (remove a C)) s.
Proof.
  induction s; intros; simpl in *; mysimp; eauto.
  assert ((remove b (remove a0 C)) = (remove a0 (remove b C))). {
    rewrite remove_comm. reflexivity. }
  rewrite H3. assumption.
  rewrite remove_comm. assumption.
  assert ((remove b (remove a0 C)) = (remove a0 (remove b C))). {
    rewrite remove_comm. reflexivity. }
  rewrite H3. assumption.
Qed.

Lemma wf_subst_remove_minus_inversion : forall B C s a, wf_subst (remove a (minus C B)) s -> wf_subst (remove a C) s.
Proof.
  induction B. intros; mysimp; simpl in *; eauto.
  intros.
  specialize IHB with (C := remove a0 C) (s := s) (a:= a).
  simpl in *.
  apply wf_subst_remove_comm in H.
  rewrite minus_remove in IHB.
  apply IHB in H.
  apply wf_subst_remove_inversion in H.
  assumption.
Qed.

Lemma wf_ty_remove_minus_inversion2 : forall s a C t, wf_ty (remove a (minus C s)) t -> wf_ty (minus C s) t.
Proof.
  induction s; intros; mysimp; simpl in *; eauto.
Qed.

Lemma wf_ty_minus_inversion : forall s C t, wf_ty (minus C s) t -> wf_ty C t.
Proof.
  induction s; intros; mysimp; simpl in *; eauto.
Qed.

Hint Resolve wf_ty_remove_inversion.

Lemma wf_ty_remove_remove : forall t C i j, wf_ty (remove i C) t -> wf_ty (remove j C) t -> wf_ty (remove i (remove j C)) t.
Proof.
  induction t.
  induction C; intros; eauto; mysimp; simpl in *; eauto.
  destruct (eq_id_dec j j); try contradiction; eauto.
  destruct (eq_id_dec j i0); try contradiction; eauto.
  simpl in H.
  destruct (eq_id_dec j i); subst; try contradiction; eauto.
  destruct (eq_id_dec i0 j); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec i0 i0); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec i0 i); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec a i0); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec a j); subst; try contradiction; simpl in *; eauto.
  intros. auto.
  intros.
  simpl in *.
  mysimp.
Qed.
  
Hint Resolve wf_ty_remove_remove.

Lemma wf_ty_remove_minus : forall s i C t, wf_ty (remove i C) t -> wf_ty (minus C (dom s)) t -> wf_ty (remove i (minus C (dom s))) t.
Proof.
  induction s; intros; eauto; mysimp; simpl in *; eauto.
Qed.

Hint Resolve wf_ty_remove_minus.
(*
  specialize IHs with (C := remove a C) (t := t).
  rewrite minus_remove in IHs.
  apply IHs; eauto.
  apply wf_ty_remove_minus_inversion in H0. 
*)
  

Lemma substs_remove_var : forall s C i, wf_subst C s ->
                                     wf_ty C (var i) ->
                                     wf_ty (minus C (dom s)) (apply_subst s (var i)).
Proof.
  induction s . intros ; simpl in *; mysimp.
  
  intros.
  destruct a.
  specialize IHs with (i := i).
  simpl in H.
  destructs H.
  simpl.
  destruct (eq_id_dec i0 i).
  - subst.
    eauto.
  -
  specialize IHs with (C := (minus C [i0])).
  simpl in *.
  cases (find_subst s i).
  + rewrite minus_remove_dist2.
    eapply IHs.
    eauto.
    eauto.
  + rewrite minus_remove_dist2.
    eauto.
Qed.

Lemma substs_remove : forall t s C , wf_subst C s ->
                                     wf_ty C t ->
                                     wf_ty (minus C (dom s)) (apply_subst s t).
Proof.
  induction t; intros; mysimp.
  rewrite apply_subst_fold.
  apply substs_remove_var; auto.
  destruct H0.
  auto.
  destruct H0.
  auto.
Qed.

Hint Resolve substs_remove substs_remove'.

Lemma apply_compose_assoc_var : forall s1 s2 s3 i, apply_subst (compose_subst (compose_subst s1 s2) s3) (var i) =
                                              apply_subst (compose_subst s1 (compose_subst s2 s3)) (var i).
Proof.
  induction s1. intros. eauto.
  intros.
  repeat rewrite apply_compose_equiv.
  reflexivity.
Qed.

Lemma len_remove_le : forall C i, length (remove i C) <= length C.
Proof.
  intros.
  induction C; simpl; auto.
  destruct (eq_id_dec a i). omega.
  simpl. omega.
Qed.

Lemma len_remove_le_S : forall C i, length (remove i C) <= S (length C).
Proof.
  intros.
  induction C; simpl; auto.
  destruct (eq_id_dec a i). omega.
  simpl. omega.
Qed.

Lemma len_minus_le : forall C a, length (minus C a) <= length C.
Proof.
    induction a.
    + simpl. auto.
    + simpl. 
      rewrite len_remove_le.
      assumption.
Qed.

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

Lemma not_member_remove : forall i a, ~ (member a i) -> remove i a = a.
Proof.
  intros.
  induction a.
  - reflexivity.
  - simpl in *. destruct (eq_id_dec a i).
    intuition.
    erewrite IHa; auto.
Qed.

Lemma member_not_member : forall C a i, member C i -> ~(member a i) -> member (minus C a) i.
Proof.
  intros.
  induction a.
  - simpl. assumption.
  - simpl in *.
    destruct (eq_id_dec a i); intuition.
Qed.

Hint Resolve member_not_member.

Lemma member_len_remove_minus' : forall C i a, member C i -> ~(member a i) -> length (remove i (minus C a)) < length (minus C a).
Proof.
  intros.
  apply remove_varctxt_length; eauto.
Qed.

Lemma len_not_member_remove : forall i a, ~(member a i) -> length a = length (remove i a).
Proof.
  intros.
  induction a; auto.
  simpl in *.
  destruct (eq_id_dec a i); intuition.
  simpl. congruence.
Qed.

Lemma aux''' : forall  (a: list id) i,  length (remove i a) <= length a.
Proof.
  induction a; intros; mysimp.
Qed.

Lemma aux'' : forall  (b a: list id) i, length b < length a -> length (remove i b) < length a.
  intros.
  pose proof (aux''' b i).
  apply Nat.lt_eq_cases in H0.
  destruct H0.
  omega.
  omega.
Qed.

Lemma member_len_minus_lt : forall s C i, member C i -> length (minus C (i::s)) < length C.
Proof.
  induction s; intros.
  - simpl in *. apply remove_varctxt_length. auto. 
  - simpl in *.
    apply IHs in H.
    destruct (eq_id_dec a i).
    + subst.
      rewrite remove_remove_inversion.
      assumption.
    + rewrite remove_comm. eapply aux''. auto.
Qed.

Hint Resolve member_len_minus_lt. 

Lemma lala : forall s C i, member (minus C (dom s)) i -> find_subst s i = None.
Proof.
  induction s; intros; simpl in *; eauto; mysimp; simpl in *.
  apply member_remove_false in H. contradiction.
  specialize IHs with (C := remove a C).
  apply IHs.
  rewrite minus_remove. auto.
Qed.

Lemma toto : forall t s1 C, wf_ty (minus C (dom s1)) t -> apply_subst s1 t = t.
Proof.
  induction t; intros.
  - simpl in H.
    apply lala in H.
    simpl. rewrite H.
    reflexivity.
  - reflexivity.
  - rewrite apply_subst_arrow.
    simpl in H. destructs H.
    fequals.
    eapply IHt1.
    apply H.
    eapply IHt2.
    apply H0.
Qed.

Lemma ria : forall s2 s1 C, wf_subst (minus C (dom s1)) s2 -> apply_subst_list s2 s1 = s2. 
Proof.
  induction s2; intros.
  reflexivity.
  simpl. destruct a.
  simpl in H.
  destructs H.
  rewrite IHs2 with (C := remove i C).
  apply wf_ty_remove_inversion in H0.
  apply toto in H0. 
  rewrite H0.
  reflexivity.
  rewrite minus_remove.
  assumption.
Qed.

Lemma apply_subst_list_dom : forall s1 s2, dom (apply_subst_list s1 s2) = dom s1.
Proof.
  induction s1; intros; mysimp; simpl in *; eauto.
  congruence.
Qed.

Lemma dom_dist_app : forall s1 s2, dom (s1 ++ s2) = (dom s1) ++ (dom s2).
Proof.
  induction s1; intros; mysimp; simpl in *; eauto.
  congruence.
Qed.

Lemma dom_dist_compose : forall s1 i t, dom (compose_subst s1 [(i, t)]) = dom s1 ++ [i].
Proof.
  induction s1; intros; mysimp; simpl in *; eauto.
  rewrite dom_dist_app.
  rewrite apply_subst_list_dom.
  simpl.
  reflexivity.
Qed.

Lemma wf_subst_last (s : substitution) : forall x t C, wf_subst C s ->
  member (minus C (dom s)) x -> wf_ty (remove x (minus C (dom s))) t ->
    wf_subst C (compose_subst s [(x,t)]).
Proof.
  induction s ; simpl ; intros . mysimp. eauto.
  destruct a. destructs H.
  simpl in *. splits; eauto.
  induction t0; mysimp; simpl in *; eauto; mysimp; eauto.
  apply wf_ty_remove_inversion in H1. apply wf_ty_remove_minus_inversion in H1. assumption.
  induction t0; mysimp; simpl in *; eauto; mysimp; eauto.
  rewrite dom_dist_app. rewrite apply_subst_list_dom. simpl.
  rewrite minus_app_comm. simpl. eauto. 
  rewrite dom_dist_app. rewrite apply_subst_list_dom. simpl.
  rewrite minus_app_comm. simpl. eauto. 
  fold (compose_subst s [(x, t)]).
  eapply IHs with (C:= remove i C); eauto.
  rewrite minus_remove. auto.
  rewrite minus_remove. auto.
Qed.

Lemma compose_cons : forall s1 s2 i t C, wf_subst C s1 -> wf_subst C ((i, t) :: s2) ->  wf_subst C (compose_subst (compose_subst s1 [(i, t)]) s2) ->
                                      wf_subst C (compose_subst s1 ((i, t) :: s2)).
Proof.
  intros.
  unfold compose_subst in *.
  rewrite arrowcons.
  assert ((apply_subst_list s1 ((i, t) :: s2) ++ [(i, t)]) = apply_subst_list (apply_subst_list s1 [(i, t)] ++ [(i, t)]) s2).
  { induction s1. simpl in *. mysimp. erewrite toto; eauto. destruct a. simpl in *. mysimp. erewrite <- IHs1; eauto. fequals. fequals. induction t0; mysimp; eauto.
    erewrite toto; eauto. simpl in *. mysimp. fequals; eauto. } 
  rewrite H2.
  fold (compose_subst s1 [(i, t)]) .
  eauto.
Qed.

Lemma member_minus_inversion : forall a C i, member (minus C a) i -> member C i.
Proof.
  induction a; intros; simpl in *; mysimp.
  eauto.
Qed.

Hint Resolve member_minus_inversion.

Lemma minus_minus_comm : forall A B C, minus (minus C A) B = minus (minus C B) A.
Proof.
  induction A. intros; repeat rewrite minus_nil2. reflexivity.
  intros.
  simpl.
  rewrite minus_remove.
  fequals.
Qed.
 
Lemma wf_subst_arrowend : forall s2 C s1,  wf_subst C s1 ->
                                         wf_subst (minus C (dom s1)) s2 ->
                                         wf_subst C (compose_subst s1 s2).
Proof.
  induction s2 ; simpl ; intros. rewrite compose_subst_nil_r ; auto.
  destruct a. destructs H0.
  eapply compose_cons; eauto. simpl. splits; eauto. apply wf_ty_remove_minus_inversion in H1. assumption. eauto.
  rewrite minus_minus_comm in H2.
  apply wf_ty_minus_inversion in H2. assumption.
  apply wf_subst_remove_minus_inversion in H3.
  assumption.
  eapply IHs2.
  eapply wf_subst_last; eauto. 
  rewrite dom_dist_compose.
  rewrite minus_app_comm.
  simpl.
  assumption.
Qed.

Hint Resolve wf_subst_arrowend.

Lemma in_list_id_new_tv_tv_lt : forall t i x st, ListIds.in_list_id x (img_ids [(i, t)]) = true -> new_tv_ty t st -> x < st.
Proof.
  induction t; intros; simpl in *; eauto.
  Unshelve. inversion H.
  inversion H.
  inversion H.
  apply i.
Qed.

Hint Resolve in_list_id_new_tv_tv_lt.

Lemma occurs_not_apply_subst_single : forall i t, ~ occurs i t -> apply_subst [(i, t)] t = t.
Proof.
  induction t; intros;
  mysimp.
  erewrite subst_occurs; eauto.
Qed.

Hint Resolve occurs_not_apply_subst_single.
Hint Rewrite occurs_not_apply_subst_single:RE.


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
  crush. omega.
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