Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Program.
Require Import SimpleTypes.
Require Import Subst.
Require Import LibTactics.
Require Import MyLtacs.


Lemma nth_error_nil : forall i, nth_error (nil : list ty) i = None.
Proof.
  intros.
  induction i; mysimp.
Qed.

Hint Resolve nth_error_nil:core.
Hint Rewrite nth_error_nil:RE.

Lemma nth_error_map : forall (s : substitution) (x : list ty) (n : id) (tau : ty),
    nth_error x n = Some tau ->
    nth_error (map_apply_subst_over_list_ty x s) n = Some (apply_subst s tau).
Proof.
  induction x; crush.
  rewrite nth_error_nil in H.
  inversion H.
  induction n; crush.
Qed.

Hint Resolve nth_error_map:core.
Hint Rewrite nth_error_map:RE.

Lemma nth_error_k_not_zero : forall a k l, k <> 0 -> nth_error ((var a)::l) k = nth_error l (pred k).
Proof.
  induction k; crush.
Qed.

Hint Resolve nth_error_k_not_zero:core.

Lemma nth_error_app_cons : forall (l : list ty) (tau : ty), nth_error (l ++ tau::nil) (length l) = Some tau.
simple induction l; auto.
Qed.

Hint Resolve nth_error_app_cons:core.

Lemma nth_error_app : forall (l l1 : list ty) (n : id), n < length l -> nth_error (l ++ l1) n = nth_error l n.
Proof.
  induction l; crush.
  induction n; crush.
  erewrite <- IHl; crush.
Qed.

Hint Resolve nth_error_app:core.
Hint Rewrite nth_error_app:RE.

