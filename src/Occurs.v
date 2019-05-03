Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import SimpleTypes.
Require Import LibTactics.
Require Import SimpleTypes.
Require Import MyLtacs.
Require Import SimpleTypes.
Require Import Program.
Require Import Subst.


(** * Occurs-check test *)

(** A predicate that specifies when a variable v occurs free in a type t *)

Fixpoint occurs (v : id) (t : ty) : Prop :=
  match t with
    | var n => if eq_id_dec n v then True else False
    | con n => False
    | SimpleTypes.arrow l r => occurs v l \/ occurs v r
  end.

(** Decidability of occurs check test *)

Definition occurs_dec : forall v t, {occurs v t} +  {~ occurs v t}.
  refine (fix occurs_dec v t : {occurs v t} +  {~ occurs v t} :=
            match t with
              | var n =>
                  if eq_id_dec n v then left _ _ else right _ _
              | con n => right _ _
              | SimpleTypes.arrow l r =>
                  match occurs_dec v l, occurs_dec v r with
                    | left _, left _ => left _ _
                    | left _, right _ => left _ _
                    | right _, left  _ => left _ _
                    | right _, right _ => right _ _
                  end
            end) ; mysimp ; intuition.
Defined.

Lemma subst_occurs : forall t v u, ~ occurs v u -> u = apply_subst ((v, t)::nil) u.
Proof.
  induction u ; mysimp ; intros ; try firstorder ; try congruence.
Qed.

Hint Resolve subst_occurs.
Hint Rewrite subst_occurs:RE.

Lemma occurs_not_apply_subst_single : forall i t, ~ occurs i t -> apply_subst [(i, t)] t = t.
Proof.
  induction t; intros;
  mysimp.
  erewrite subst_occurs; eauto.
Qed.

Hint Resolve occurs_not_apply_subst_single.
Hint Rewrite occurs_not_apply_subst_single:RE.

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
