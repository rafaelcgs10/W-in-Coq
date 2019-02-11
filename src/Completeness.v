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
Require Import MoreGeneral.

Require Import LibTactics.

Lemma id_increases_in_w : forall (e : term) (i i' : id) (G : ctx) (tau : ty)
    (s : substitution),
    getResult (runInfer_id e G i) = Some (i', tau, s) -> i <= i'.
Admitted.

Lemma new_tv_W: forall (e : term) (G : ctx) (i i': id) (t : ty) (s : substitution),
    (new_tv_ctx G i) -> getResult (runInfer_id e G i) = Some (i, t, s) ->
    new_tv_ty t i' /\ new_tv_subst s i'.
Admitted.

Lemma completeness : forall (e : term) (G : ctx) (tau' : ty) (phi : substitution) (i : id),
    has_type (apply_subst_ctx phi G) e tau' -> new_tv_ctx G i ->
    exists s tau i' s', getResult (runInfer_id e G i) = Some (i', tau, s) /\
    tau' = apply_subst s' tau /\
    (forall x : id, x < i -> apply_subst phi (var x) = apply_subst (s ++ s') (var x)).
Proof.
  intros.
  induction e.
  admit.
  admit.
  admit.
  admit.
  - inversion H.
    simpl.
    (** rever a parte do algoritmo que infere constantes *)
    exists (nil : substitution) (con 0) i (nil : substitution).
    simpl. split; try reflexivity.

Admitted.
