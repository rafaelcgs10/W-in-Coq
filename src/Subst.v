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

Definition FV_subst (s: substitution) := ((dom s) ++ (img_ids s)).

Fixpoint id_in_subst (i : id) (s : substitution) : option ty :=
  match s with
    | nil => None
    | (i', tau)::s' => if eq_id_dec i i' then Some tau else id_in_subst i s'
  end.

