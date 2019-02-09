Set Implicit Arguments.

Require Import Unify.
Require Import Schemes.
Require Import List.
Require Import ListIds.
Require Import Context.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Typing.
Require Import Infer.
Require Import NewTypeVariable.

Require Import LibTactics.

Lemma id_increases_in_w : forall (e : term) (i i' : id) (G : ctx) (t : ty) (s : substitution),
                            getState (runInfer_id e G i) = Some i' -> i <= i'.
  Admitted.

Lemma new_tv_W: forall (e : term) (G : ctx) (i i': id) (t : ty) (s : substitution)
                  rs,
    (new_tv_ctx G i) -> (runInfer_id e G i) = rs -> getState rs = Some i' ->
    getResult rs = Some (t, s).

