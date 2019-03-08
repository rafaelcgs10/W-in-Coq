Set Implicit Arguments.

Require Import Unify.
Require Import Schemes.
Require Import Omega.
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

(*
Lemma id_increases_in_w : forall (e : term) (i i' : id) (G : ctx) (tau : ty)
    (s : substitution),
    getResult (runInfer_id e G i) = Some (i', tau, s) -> i <= i'.
Admitted.

Lemma new_tv_W: forall (e : term) (G : ctx) (i i': id) (t : ty) (s : substitution),
    (new_tv_ctx G i) -> getResult (runInfer_id e G i) = Some (i, t, s) ->
    new_tv_ty t i' /\ new_tv_subst s i'.
Admitted.
*)

Ltac destructMatch :=
  match goal with
    | [ |- context[match ?a with  | _ => _ end] ] => cases a
  end.


Lemma list_ty_and_id_inv : forall lt_st : list ty * id,
    {lt_st1 : list ty * id | lt_st1 = lt_st}.
Proof.
intros lt_st; exists lt_st; auto.
Qed.


Lemma apply_compute_gen_subst : forall (st : id) (sigma : schm) (p : nat),
    max_gen_vars sigma <= p ->
    {tau : ty | apply_inst_subst (fst (compute_generic_subst st p)) sigma = Some_schm tau}.
Admitted.

Fixpoint id_in_subst (i : id) (s : substitution) : option ty :=
  match s with
    | nil => None
    | (i', tau)::s' => if eq_id_dec i i' then Some tau else id_in_subst i s'
  end.

Lemma apply_subst_app : forall (s1 s2 : substitution) (st : id),
 id_in_subst st s1 = None -> apply_subst (s1 ++ s2) (var st) = apply_subst s2 (var st).
Admitted.

Lemma not_in_domain_compute : forall (sg : list ty) (x st : id), x < st ->
 id_in_subst x (compute_subst st sg) = None.
Admitted.

Lemma apply_app_compute_subst :
 forall (s0 : substitution) (st i : id) (sg : list ty),
 i < st -> apply_subst (compute_subst st sg ++ s0) (var i) = apply_subst s0 (var i).
Proof.
intros; apply apply_subst_app.
apply not_in_domain_compute; auto.
Qed.

Fixpoint W (st : id) (e : term) (G : ctx) {struct e} : option (ty * substitution * id) :=
  match e with
  | var_t x => match in_ctx x G with
              | None => None
              | Some sigma =>
                 match compute_generic_subst st (max_gen_vars sigma) with
                 | (l, st') =>
                     match apply_inst_subst l sigma with
                     | Error_schm => None 
                     | Some_schm tau => Some (tau, nil, st')
                     end
                 end
              end
  | _ => Some (var 0, nil, 0)
  end. 

Lemma completeness' : forall (e : term) (G : ctx) (tau' : ty) (phi : substitution) (st : id),
    has_type (apply_subst_ctx phi G) e tau' -> new_tv_ctx G st ->
    exists s tau st', W st e G  = Some (tau, s, st')  /\
    exists s', tau' = apply_subst s' tau /\
    (forall x : id, x < st -> apply_subst phi (var x) = apply_subst (s ++ s') (var x)).
Proof.
  intros.
  induction e.
  - inversion H.
    subst.
    simpl.
    destruct (assoc_subst_exists G i phi H2) as [sigma' H2'].
    destruct H2' as [H21  H22].
    rewrite H21.
    destruct (list_ty_and_id_inv (compute_generic_subst st (max_gen_vars sigma'))) as [s_id H3].
    destruct s_id as [s id].
    rewrite <- H3.
    simpl.
    edestruct (apply_compute_gen_subst st sigma') with (p := max_gen_vars sigma') as [tau H5].
    omega.
    sort.
    assert (s = fst (compute_generic_subst st (max_gen_vars sigma'))) as H6.
    { rewrite surjective_pairing in H3. inversion H3. reflexivity. }
    rewrite H6.
    rewrite H5.
    exists (nil:substitution) tau id.
    splits; auto.
    inversion H4.
    exists (compute_subst st x ++ phi).
    split.
    + eapply t_is_app_T_aux with (p := max_gen_vars sigma').
      eapply new_tv_ctx_implies_new_tv_schm.
      apply H21.
      auto.
      auto.
      auto.
      rewrite H22 in H1.
      auto.
    + intros.
      simpl.
      symmetry.
      eapply apply_app_compute_subst;
      auto.
  -




  
