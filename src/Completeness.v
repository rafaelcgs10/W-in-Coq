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

Ltac destructMatch :=
  match goal with
    | [ |- context[match ?a with  | _ => _ end] ] => cases a
  end.

Lemma assoc_subst_exists : forall (G : ctx) (i : id) (s : substitution) (sigma : schm),
    in_ctx i (apply_subst_ctx s G) = Some sigma ->
    {sigma' : schm | in_ctx i G = Some sigma' /\ sigma = apply_subst_schm s sigma'}.
Proof.
Admitted.

Lemma in_ctx_to_look_dep : forall i G sigma (ev : in_ctx i G = Some sigma),
    look_dep i G = ret (exist _ sigma ev).
Proof.
  intros.
  unfold look_dep.
  destruct (in_ctx i G).
  inversion ev.
  subst.
  fequals.
  fequals.
  inversion ev.
Qed.

Lemma list_ty_and_id_inv : forall lt_st : list ty * id,
    {lt_st1 : list ty * id | lt_st1 = lt_st}.
Proof.
intros lt_st; exists lt_st; auto.
Qed.

Fixpoint compute_gen_subst (i : id) (n : nat) : (list ty) * id :=
  match n with
  | O => (nil, i)
  | S p => match compute_gen_subst (S i) p with
      | (l, i') => (var i :: l, i')
      end
  end.

Fixpoint max_gen_vars (sigma : schm) : nat :=
  match sigma with
  | sc_con _ => 0
  | sc_var _ => 0
  | sc_gen i => S i
  | sc_arrow s1 s2 => max (max_gen_vars s1) (max_gen_vars s2)
  end.

Lemma apply_compute_gen_subst : forall (i : id) (sigma : schm) (p : nat) is,
    {tau : ty | apply_inst_subst is sigma = Some_schm tau}.
Admitted.

Lemma completeness : forall (e : term) (G : ctx) (tau' : ty) (phi : substitution) (i : id),
    has_type (apply_subst_ctx phi G) e tau' -> new_tv_ctx G i ->
    exists s tau i' s', getResult (runInfer_id e G i) = Some (i', tau, s) /\
    tau' = apply_subst s' tau /\
    (forall x : id, x < i -> apply_subst phi (var x) = apply_subst (s ++ s') (var x)).
Proof.
  intros.
  induction e.
  - unfold runInfer_id.
    inversion H.
    (** ver o tipo de i0 em S(G) e quem ele é sem S*)
    destruct (assoc_subst_exists G i0 phi H2).
    destruct a.
    (** usar na computação a informação de quem é o tipo de i0 *)
    pose proof (in_ctx_to_look_dep i0 G H6).
    unfold infer_dep.
    rewrite H8.
    cbn.

    unfold schm_inst_dep.
    assert (exists s, mapM (fun _ : id => fresh) (list_bounds_ids x0) = ret s).
    skip.
    destruct H9.
    cases x0.
    + remember H9 as H9'.
      simpl in H9.
      assert (forall (x y : list ty), ret x = ret y -> x = y).  
      skip.
      clear HeqH9'.
      eapply H10 in H9.
      subst.
      rewrite H9'.
      simpl.
      exists (nil:substitution) (var i1) i.
      exists ((i1, tau')::nil : substitution).
      splits; mysimp.
      intros.
      mysimp.
      destruct H4.
      simpl in H3.
      subst.
      skip.
      
      unfold ret in H9, H10.
      
      Unset Printing Notations.
      
      f_equal

      inversion H9.

    simpl.
   
    comp
    lazy.
    rewrite H9.
    pose proof
    
    pose proof (schm_inst_dep x0 (mkState i)).
    destruct H9.
    destruct p.
    destruct s.
    simpl.
    sort.
    (** descobrir qual é a substituição que calcula a instância de x0 *)
    subst.
    destruct M.
    destruct p.
    pose proof (schm_inst_dep x0 (mkState i)).
    destruct H1.
    destruct p.
    destruct s.
    unfold is_schm_instance in i1.
    destruct i1.
    substs.
    assert ((max_gen_vars x0) <= i). admit.
    destruct (apply_compute_gen_subst i x H5).

    compu
    
    simpl.

    
    subst.
    cases (infer_dep (var_t i0) G {| next_tvar := i |}).
    destruct p.
    destruct t.
    destruct s.
    destruct s.
    exists x0 x next_tvar.

    destructs a.
    simpl.
    pose proof in_ctx_look_def i0 G H1 as IN1. 
    rewrite IN1.
    sort.
    destruct (list_ty_and_id_inv (compute_gen_subst i (max_gen_vars x))) as [GEN GENC].
    destructMatch.
    destruct p.
    destruct t.
    destruct s.
    destruct s.
    clear Eq.

    exists x1 x0 next_tvar.
    subst.
    destruct H4.
    

    simpl in e0.

    destruct s.
    inversion h.
    subst.
    destruct (assoc_subst_exists G i0 x1 H6).
    destructs a.
    pose proof in_ctx_look_def i0 G H3 as IN2. 
    exists x1 x0 next_tvar x1.
    splits.
    reflexivity.

    simpl.
    destruct sigma_dep.
    
  admit.
  admit.
  admit.
  admit.
  - admit.
