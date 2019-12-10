(** * The simple type substitution
      This file contains the defintion of simple type substitution [substitution] and 
      some auxiliary definitions.
    *)

Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Import ListNotations.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import SimpleTypes.
Require Import SimpleTypesNotations.
Require Import LibTactics.
Require Import MyLtacs.

(** * Substitutions *)

Definition substitution := list (id * ty).

(** Notations for substitutions in the custom entry   *)
Notation "[ ]" := (nil:substitution) (in custom DM at level 1).
Notation "[ e ]" := e (in custom DM, e at level 4).
Notation "a ; .. ; b" := ((cons a .. (cons b nil) ..):substitution)
  (in custom DM at level 7, a custom DM at next level, b custom DM at next level).
Notation "i => t" := (i, t)
  (in custom DM at level 6, i constr at level 5, t constr at level 5).

(** A look up function to find in [s] the identifier [i]. *)
Fixpoint find_subst (s : list (id * ty)) (i : id) : option ty :=
  match s with
    | nil => None
    | (v,t') :: s' => if (eq_id_dec v i) then Some t' else find_subst s' i
  end.

(** The application substitution operation, which is non-incremental. *)
Fixpoint apply_subst (s : substitution) (t : ty) : ty :=
  match t with
  | &[l -> r] => &[({apply_subst s l}) -> ({apply_subst s r})]
  | var i => match find_subst s i with
            | None => var i
            | Some t' => t'
            end
  | con i => con i
  end.

(** Notation for the substitution applicatio *)
Notation "S ( t )" := (apply_subst S t) (in custom DM at level 2, S constr, t constr at level 1).

(** * Substitution and its projections *)

Definition dom (s : substitution) : list id := map (@fst id ty) s.
Definition img (s : substitution) : list ty := map (@snd id ty) s.
Definition img_ids (s : substitution) : list id := concat (map ids_ty (img s)).

Lemma img_ids_append_cons : forall (i :id) (t : ty) (s : substitution),
    img_ids ((i, t)::s) = ids_ty t ++ img_ids s.
Proof.
  induction t; mysimp.
Qed.

(** ** Free variables of a substitution *)

Definition FV_subst (s: substitution) := ((dom s) ++ (img_ids s)).

Notation "FV( s )" := (FV_subst s) (in custom DM at level 0, s constr at level 1).

(** ** Some lemas retaled to the domain of a substitution *)

Lemma dom_dist_app : forall s1 s2, dom (s1 ++ s2) = (dom s1) ++ (dom s2).
Proof.
  induction s1; intros; mysimp; simpl in *; eauto.
  congruence.
Qed.

Lemma ids_ty_apply_subst : forall (S : substitution) (tau : ty),
    (ids_ty (&[ S(tau) ])) =
    concat (map ids_ty ( (map (apply_subst S) (map var (ids_ty tau))))).
Proof.
  intros.
  induction tau; mysimp.
  rewrite app_nil_r. reflexivity.
  repeat rewrite map_app.
  repeat rewrite concat_app.
  rewrite <- IHtau1.
  rewrite <- IHtau2.
  reflexivity.
Qed.

(** ** Some obvious facts about substitutions **)

Lemma apply_subst_con : forall (S : substitution) (n : id), &[ S({con n})] = con n.
Proof.
  induction S ; mysimp.
Qed.

Hint Resolve apply_subst_con:core.
Hint Rewrite apply_subst_con:RE.

Lemma apply_subst_arrow : forall (S : substitution) (l r : ty),
    &[ S(l -> r) ] = &[ S(l) -> S(r) ].
Proof.
  induction S ; mysimp.
Qed.

Hint Resolve apply_subst_arrow:core.
Hint Rewrite apply_subst_arrow:RE.

Lemma apply_subst_nil : forall tau, &[ [ ](tau) ] = tau.
Proof.
  intros; induction tau; mysimp.
  congruence.
Qed.

Hint Resolve apply_subst_nil:core.
Hint Rewrite apply_subst_nil:RE.

Lemma arrow_subst_eq : forall (l l' r r' : ty) (S : substitution),
    &[ S(l) ] = &[ S(l') ] ->
    &[ S(r) ] = &[ S(r') ] ->
    &[ S(l -> r) ] = &[ S(l' -> r') ].
Proof.
  intros ; do 2 rewrite apply_subst_arrow ; fequals*.
Qed.

Hint Resolve arrow_subst_eq:core.

(** Some lemmas for folding back a substitution application *)
Lemma apply_subst_fold : forall (S : substitution),
    (forall i, match find_subst S i with | Some t' => t' | None => var i end = &[ S({var i}) ]).
Proof.
  intros. reflexivity.
Qed.

Lemma apply_subst_fold2 :  forall S S',
    (forall i, match find_subst S i with | Some t' => t' | None => var i end =
          match find_subst S' i with | Some t' => t' | None => var i end) <->
    forall i, &[ S({var i}) ] = &[ S'({var i}) ].
Proof.
  intros; split; intro; 
    simpl in *;
    auto.
Qed.


(** * Apply substitution over a list (over another substitution) **)

Fixpoint apply_subst_list (s1 s2 : substitution) : substitution :=
  match s1 with
  | nil => nil
  | (i, t)::s1' => (i, apply_subst s2 t)::apply_subst_list s1' s2
  end.

(** Notation for substitution application over another substitution *)
Notation "S (- S' -)" := (apply_subst_list S S') (in custom DM at level 2, S constr, S' constr at level 1).

(** ** Some lemmas about [apply_subst_list] **)

Lemma apply_subst_list_dom : forall (S1 S2 : substitution),
    dom &[ S1(- S2 -) ] = dom S1.
Proof.
  induction S1; intros; mysimp; simpl in *; eauto.
  congruence.
Qed.

Hint Resolve apply_subst_list_dom:core.
Hint Rewrite apply_subst_list_dom:RE.

Lemma apply_subst_list_nil : forall (S : substitution),
    &[ S(- [ ] -) ] = S.
Proof.
  induction S; mysimp.
  rewrite apply_subst_nil.
  congruence.
Qed.

Hint Resolve apply_subst_list_nil:core.
Hint Rewrite apply_subst_list_nil:RE.

Lemma dom_app_dist : forall (S1 S2 : substitution),
    dom (S1 ++ S2) = dom S1 ++ dom S2.
Proof.
  induction S1; crush.
Qed.

Hint Resolve dom_app_dist:core.
Hint Rewrite dom_app_dist:RE.

Lemma img_app_dist : forall (S1 S2 : substitution),
   img (S1 ++ S2) = img S1 ++ img S2.
Proof.
  induction S1; crush.
Qed.

Hint Resolve img_app_dist:core.
Hint Rewrite img_app_dist:RE.

Lemma img_ids_app_dist : forall (S1 S2 : substitution),
    img_ids (S1 ++ S2) = img_ids S1 ++ img_ids S2.
Proof.
  unfold img_ids.
  intros.
  rewrite <- concat_app.
  rewrite img_app_dist. 
  rewrite map_app.
  reflexivity.
Qed.

Hint Resolve img_ids_app_dist:core.
Hint Rewrite img_ids_app_dist:RE.

(** * Substitution composition *)

Definition compose_subst (S1 S2 : substitution) :=
  &[ S1(- S2 -) ] ++ S2.

(** Notation for substitution composition *)
Notation "S1 'o' S2" := (compose_subst S1 S2)
      (in custom DM at level 3, S1 constr, S2 constr, left associativity).

(** ** Some obvious facts about composition **)

Lemma compose_subst_nil_l : forall (S : substitution),
    &[ [ ] o S ] = S.
Proof.
  intros; induction S; mysimp.
Qed.

Hint Resolve compose_subst_nil_l:core.
Hint Rewrite compose_subst_nil_l:RE.

Lemma compose_subst_nil_r : forall (S : substitution),
    &[ S o [ ] ] = S.
Proof.
  induction S; unfold compose_subst in *; crush.
Qed.

Hint Resolve compose_subst_nil_r:core.
Hint Rewrite compose_subst_nil_r:RE.

Lemma apply_compose_subst_nil_l : forall (S : substitution) (tau : ty),
    &[ ([ ] o S)(tau) ] = &[ S(tau) ].
Proof.
  intros; mysimp. 
Qed.

Hint Resolve apply_compose_subst_nil_l:core.
Hint Rewrite apply_compose_subst_nil_l:RE.

Lemma apply_compose_subst_nil_r : forall (S : substitution) (tau : ty),
    &[ (S o [ ])(tau) ] = &[ S(tau) ].
Proof.
  intros; mysimp; induction S; autorewrite with RE using congruence.
Qed.

Hint Resolve apply_compose_subst_nil_r:core.
Hint Rewrite apply_compose_subst_nil_r:RE.

(** More lemmas about substitution composition *)
Lemma apply_compose_equiv : forall (S1 S2 : substitution) (tau : ty),
    &[ (S1 o S2)(tau) ] = &[ S2(S1(tau)) ].
Proof.
  induction S1; intros; mysimp.
  repeat rewrite apply_compose_subst_nil_l.  autorewrite with RE using congruence.
  induction tau; mysimp; simpl in *; eauto.
  repeat rewrite apply_subst_fold.
  erewrite <- IHS1.
  simpl.
  unfold compose_subst. reflexivity.
  fequals.
Qed.

Hint Resolve apply_compose_equiv:core.
Hint Rewrite apply_compose_equiv:RE.

Lemma apply_compose_assoc_var : forall s1 s2 s3 i,
    apply_subst (compose_subst (compose_subst s1 s2) s3) (var i) =
    apply_subst (compose_subst s1 (compose_subst s2 s3)) (var i).
Proof.
  induction s1. intros. eauto.
  intros.
  repeat rewrite apply_compose_equiv.
  reflexivity.
Qed.

(** Lemma about the domain of substitution composition *)
Lemma dom_dist_compose : forall s1 i t, dom (compose_subst s1 [(i, t)]) = dom s1 ++ [i].
Proof.
  induction s1; intros; mysimp; simpl in *; eauto.
  rewrite dom_dist_app.
  rewrite apply_subst_list_dom.
  simpl.
  reflexivity.
Qed.

(** * Lemma about free variables of a composed substitution *)

Lemma FV_subst_compose : forall s1 s2,
    FV_subst (compose_subst s1 s2) = FV_subst ((apply_subst_list s1 s2) ++ s2).
Proof.
  induction s1; crush.
Qed.

(** ** find_subst lemmas *)

Lemma find_subst_none_apply_app : forall (s1 s2 : substitution) (st : id),
    find_subst s1 st = None -> apply_subst (s1 ++ s2) (var st) = apply_subst s2 (var st).
Proof.
  induction s1;
  crush.
Qed.

Hint Resolve find_subst_none_apply_app:core.
Hint Rewrite find_subst_none_apply_app:RE.

Lemma find_subst_some_apply_app : forall (s1 s2 : substitution) (st : id) (tau : ty),
    find_subst s1 st = Some tau -> apply_subst (s1 ++ s2) (var st) = tau.
Proof.
  induction s1; crush.
Qed.

Hint Resolve find_subst_some_apply_app:core.
Hint Rewrite find_subst_some_apply_app:RE.

Lemma find_subst_some_app : forall (s1 s2 : substitution) (st : id) (tau : ty),
 find_subst s1 st = Some tau -> find_subst (s1 ++ s2) st = Some tau.
Proof.
  intros. induction s1; crush.
Qed.

Hint Resolve find_subst_some_app:core.
Hint Rewrite find_subst_some_app:RE.


Lemma find_subst_none_apply_compose : forall (s1 s2 : substitution) (st : id),
 find_subst s1 st = None -> apply_subst (compose_subst s1 s2) (var st) = apply_subst s2 (var st).
Proof.
  intros.
  induction s1.
  - mysimp.
  - simpl in *.
    destruct a.
    mysimp.
Qed.

Hint Resolve find_subst_none_apply_compose:core.
Hint Rewrite find_subst_none_apply_compose : subst.
 
(** ** Some lemmas about substitution application over a variable *)

Lemma add_subst_rewrite_for_modified_id : forall (s : substitution) (i : id) (tau : ty),
    (apply_subst ((i, tau)::s) (var i)) = tau.
  intros.
  mysimp.
Qed.

Hint Resolve add_subst_rewrite_for_modified_id:core.

Lemma add_subst_rewrite_for_unmodified_id : forall (s : substitution) (i j : id) (tau : ty),
    i <> j -> (apply_subst ((i, tau):: s)) (var j) = apply_subst s (var j).
  intros; induction s; mysimp.
Qed.

Hint Resolve add_subst_rewrite_for_unmodified_id:core.

(** * Extensionality Lemmas For Substitutions *)

Lemma ext_subst_var_ty : forall s s', (forall v, apply_subst s (var v) = apply_subst s' (var v)) ->
                                 forall t, apply_subst s t = apply_subst s' t.
Proof.
  intros ; induction t; mysimp;
    try (do 2 rewrite apply_subst_arrow) ;
    simpl in *; auto; try (do 2 rewrite apply_subst_con); auto.
  try (rewrite IHt1 ; auto). try (rewrite IHt2 ; auto).
Qed.

(** * Creates a list of type from a list of ids *)

Fixpoint ty_from_id_list (l : list id) : list ty :=
  match l with
  | nil => nil
  | x::l' => var x :: ty_from_id_list l'
  end.

Lemma length_ty_from_id_list : forall l : list id, length (ty_from_id_list l) = length l.
Proof.
  induction l; simpl; auto.
Qed.

Hint Resolve length_ty_from_id_list:core.
Hint Rewrite length_ty_from_id_list:RE.

Lemma ty_from_id_list_app : forall l1 l2 : list id,
    ty_from_id_list (l1 ++ l2) = ty_from_id_list l1 ++ ty_from_id_list l2.
Proof.
  induction l1; crush. 
Qed.

Hint Resolve ty_from_id_list_app:core.
Hint Rewrite ty_from_id_list_app:RE.

(** * Map simple substitution over a list of ty *)

(** This is different from [apply_subst_list] *)
Fixpoint map_apply_subst_over_list_ty (l : list ty) (s2 : substitution) :=
  match l with
  | nil => nil
  | t::l' => apply_subst s2 t :: map_apply_subst_over_list_ty l' s2
  end.

(** ** Lemmas about [apply_subst_list] *)

Lemma map_extend_app : forall (s : substitution) (l1 l2 : list ty),
    map_apply_subst_over_list_ty (l1 ++ l2) s = map_apply_subst_over_list_ty l1 s ++ map_apply_subst_over_list_ty l2 s.
Proof.
  induction l1; crush.
Qed.

Hint Resolve map_extend_app:core.
Hint Rewrite map_extend_app:RE.

Lemma length_map : forall (s : substitution) (l : list ty),
    length (map_apply_subst_over_list_ty l s) = length l.
Proof.
  induction l; simpl; auto.
Qed.

Hint Resolve length_map:core.
Hint Rewrite length_map:RE.

Lemma length_map2 : forall (s : substitution) (l : list id),
    length (map_apply_subst_over_list_ty (ty_from_id_list l) s) = length l.
Proof.
  simple induction l; auto.
  intros; simpl in |- *.
  rewrite H; auto.
Qed.

Hint Resolve length_map2:core.
Hint Rewrite length_map2:RE.

Lemma app_length_cons : forall (A : Set) (l : list A) (x : A), length (l ++ x :: nil) = S (length l).
Proof.
  simple induction l; auto.
  intros; simpl in |- *; auto.
Qed.

Hint Resolve app_length_cons:core.
Hint Rewrite app_length_cons:RE.
