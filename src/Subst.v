Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Program.
Require Import SimpleTypes.
Require Import LibTactics.
Require Import MyLtacs.

(** * Substitutions *)

(** A operation for substitute all the ocurrences of variable x in t2 by t1. *)
Definition substitution := list (id * ty).

(** find_subst is in MyLtacs because I'm lazy!*)

Fixpoint apply_subst (s : substitution) (t : ty) : ty :=
  match t with
  | arrow l r => arrow (apply_subst s l) (apply_subst s r)
  | var i => match find_subst s i with
            | None => var i
            | Some t' => t'
            end
  | con i => con i
  end.

(** ** Substitution Definitions and Its Well Formedness Predicate *)

(** Substitution and its dom *)

Definition dom (s : substitution) : list id := List.map (@fst id ty) s.
Definition img (s : substitution) : list ty := List.map (@snd id ty) s.
Definition img_ids (s : substitution) : list id := List.concat (List.map ids_ty (img s)).

(** ** Some Obvious Facts About Substitutions **)

Lemma apply_subst_id : forall t, apply_subst nil t = t.
Proof.
  induction t ; mysimp.
  congruence.
Qed.

Hint Resolve apply_subst_id.
Hint Rewrite apply_subst_id:RE.

Lemma apply_subst_con : forall s n, apply_subst s (con n) = con n.
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_con.
Hint Rewrite apply_subst_con:RE.

Lemma apply_subst_arrow : forall s l r, apply_subst s (arrow l r) = arrow (apply_subst s l) (apply_subst s r).
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_arrow.
Hint Rewrite apply_subst_arrow:RE.

(** ** Substitution composition **)
Fixpoint in_subst_b (i : id) (s : substitution) : bool :=
  match s with
  | nil => false
  | (j, _)::s' => if eq_id_dec i j then true else in_subst_b i s'
  end.

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
Hint Rewrite apply_subst_nil:RE.

Lemma apply_subst_list_nil : forall s, apply_subst_list s nil = s.
Proof.
  induction s; mysimp.
  rewrite apply_subst_nil.
  congruence.
Qed.

Hint Resolve apply_subst_list_nil.
Hint Rewrite apply_subst_list_nil:RE.

Definition compose_subst (s1 s2 : substitution) :=
      apply_subst_list s1 s2 ++ s2.

Lemma compose_subst_nil_l : forall s, compose_subst nil s = s.
Proof.
  intros; induction s; mysimp.
Qed.

Hint Resolve compose_subst_nil_l.
Hint Rewrite compose_subst_nil_l:RE.

Lemma compose_subst_nil_r : forall s, compose_subst s nil = s.
Proof.
  induction s; unfold compose_subst in *; crush.
Qed.

Hint Resolve compose_subst_nil_r.
Hint Rewrite compose_subst_nil_r:RE.

(** ** Some Obvious Facts About Composition **)

Lemma apply_compose_subst_nil_l : forall s t, apply_subst (compose_subst nil s) t = apply_subst s t.
Proof.
  intros; mysimp. 
Qed.

Hint Resolve apply_compose_subst_nil_l.
Hint Rewrite apply_compose_subst_nil_l:RE.

Lemma apply_compose_subst_nil_r : forall s t, apply_subst (compose_subst s nil) t = apply_subst s t.
Proof.
  intros; mysimp; induction s; autorewrite with RE using congruence.
Qed.

Hint Resolve apply_compose_subst_nil_r.
Hint Rewrite apply_compose_subst_nil_r:RE.

Lemma apply_subst_fold : forall s, (forall i, match find_subst s i with | Some t' => t' | None => var i end = apply_subst s (var i)).
Proof.
  intros. reflexivity.
Qed.

Lemma apply_subst_fold2 :  forall s s', (forall i, match find_subst s i with | Some t' => t' | None => var i end =
                                         match find_subst s' i with | Some t' => t' | None => var i end) <->
                                   (forall i, apply_subst s (var i) = apply_subst s' (var i)).
Proof.
  intros; split; intro; 
    simpl in *;
    auto.
Qed.

Lemma apply_compose_equiv : forall s1 s2 t, apply_subst (compose_subst s1 s2) t = apply_subst s2 (apply_subst s1 t).
Proof.
  induction s1; intros; mysimp. repeat rewrite apply_compose_subst_nil_l.  autorewrite with RE using congruence.
  induction t; mysimp; simpl in *; eauto.
  repeat rewrite apply_subst_fold.
  erewrite <- IHs1.
  simpl.
  unfold compose_subst. reflexivity.
  fequals.
Qed.

Hint Resolve apply_compose_equiv.
Hint Rewrite apply_compose_equiv:RE.

(** ** Extensionality Lemmas For Substitutions *)

Lemma ext_subst_var_ty : forall s s', (forall v, apply_subst s (var v) = apply_subst s' (var v)) ->
                                       forall t, apply_subst s t = apply_subst s' t.
Proof.
  intros ; induction t ; mysimp ; try (do 2 rewrite apply_subst_arrow) ;
     simpl in * ; auto ; try (do 2 rewrite apply_subst_con) ; auto.
    try (rewrite IHt1 ; auto). try (rewrite IHt2 ; auto).
Qed.

Definition FV_subst (s: substitution) := ((dom s) ++ (img_ids s)).

Fixpoint id_in_subst (i : id) (s : substitution) : option ty :=
  match s with
    | nil => None
    | (i', tau)::s' => if eq_id_dec i i' then Some tau else id_in_subst i s'
  end.

Lemma arrow_subst_eq : forall l l' r r' s,  apply_subst s l = apply_subst s l' ->
                                          apply_subst s r = apply_subst s r' ->
                                          apply_subst s (arrow l r) = apply_subst s (arrow l' r').
Proof.
  intros ; do 2 rewrite apply_subst_arrow ; fequals*.
Qed.

Hint Resolve arrow_subst_eq.

Lemma apply_compose_assoc_var : forall s1 s2 s3 i, apply_subst (compose_subst (compose_subst s1 s2) s3) (var i) =
                                              apply_subst (compose_subst s1 (compose_subst s2 s3)) (var i).
Proof.
  induction s1. intros. eauto.
  intros.
  repeat rewrite apply_compose_equiv.
  reflexivity.
Qed.

Lemma apply_subst_lit_dom : forall s1 s2, dom (apply_subst_list s1 s2) = dom s1.
Proof.
  induction s1; intros; mysimp; simpl in *; eauto.
  congruence.
Qed.

Lemma dom_dist_app : forall s1 s2, dom (s1 ++ s2) = (dom s1) ++ (dom s2).
Proof.
  induction s1; intros; mysimp; simpl in *; eauto.
  congruence.
Qed.

Lemma apply_subst_list_dom : forall s1 s2, dom (apply_subst_list s1 s2) = dom s1.
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

Lemma apply_subst_app : forall (s1 s2 : substitution) (st : id),
    find_subst s1 st = None -> apply_subst (s1 ++ s2) (var st) = apply_subst s2 (var st).
Proof.
  induction s1;
  crush.
Qed.

Hint Resolve apply_subst_app.
Hint Rewrite apply_subst_app:RE.

Lemma apply_app : forall (s1 s2 : substitution) (st : id) (tau : ty),
    find_subst s1 st = Some tau -> apply_subst (s1 ++ s2) (var st) = tau.
Proof.
  induction s1; crush.
Qed.

Hint Resolve apply_app.
Hint Rewrite apply_app:RE.

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

Lemma img_ids_append_cons : forall a t s, img_ids ((a, t)::s) = ids_ty t ++ img_ids s.
Proof.
  induction t; mysimp.
Qed.

