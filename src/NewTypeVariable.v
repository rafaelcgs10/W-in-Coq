Set Implicit Arguments.

Require Import SimpleTypes.
Require Import Gen.
Require Import Omega.
Require Import Schemes.
Require Import List.
Require Import MyLtacs.
Require Import Subst.
Require Import ListIds.
Require Import Context.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.

Require Import LibTactics.

Inductive new_tv_ty : ty -> id -> Prop :=
| new_tv_con : forall i i' : id, new_tv_ty (con i') i
| new_tv_var : forall i i' : id, i < i' -> new_tv_ty (var i) i'
| new_tv_arrow : forall (tau tau' : ty) (i : id), new_tv_ty tau i ->
                                             new_tv_ty tau' i ->
                                             new_tv_ty (arrow tau tau') i.

Hint Constructors new_tv_ty.

Inductive new_tv_schm : schm -> id -> Prop :=
| new_tv_sc_con : forall i i' : id, new_tv_schm (sc_con i') i
| new_tv_sc_var : forall i i' : id, i < i' -> new_tv_schm (sc_var i) i'
| new_tv_sc_gen : forall i i' : id, new_tv_schm (sc_gen i') i
| new_tv_sc_arrow : forall (tau tau' : schm) (i : id), new_tv_schm tau i ->
                                               new_tv_schm tau' i ->
                                               new_tv_schm (sc_arrow tau tau') i.

Hint Constructors new_tv_schm.

Inductive new_tv_ctx : ctx -> id -> Prop :=
| new_tv_ctx_nil : forall i : id, new_tv_ctx nil i
| new_tv_ctx_cons : forall (G : ctx) (i x : id) (sigma : schm),
                            new_tv_ctx G i ->
                            new_tv_schm sigma i ->
                            new_tv_ctx ((x, sigma) :: G) i.

Hint Constructors new_tv_ctx.

Inductive new_tv_subst : substitution -> id -> Prop :=
| new_tv_subst_intro : forall (i : id) (s : substitution),
                  (forall x : id, in_list_id x (FV_subst s) = true -> x < i) ->
                  new_tv_subst s i.

Hint Constructors new_tv_subst.

Lemma new_tv_compose_subst : forall (s1 s2 : substitution) (i : id),
                             new_tv_subst s1 i ->
                             new_tv_subst s2 i ->
                             new_tv_subst (compose_subst s1 s2) i.
Admitted.

Hint Resolve new_tv_compose_subst.

Lemma new_tv_subst_nil : forall st, new_tv_subst nil st.
Proof.
  intros. econstructor; intros ; simpl in *; inversion H.
Qed.

Hint Resolve new_tv_subst_nil.

Lemma new_tv_schm_to_new_tv_ty : forall sigma x x0 i, new_tv_schm sigma x ->
                          apply_inst_subst (compute_inst_subst x i) sigma = Some_schm x0 ->
                          new_tv_ty x0 (x + i).
Proof.
  induction sigma; intros; simpl in *; mysimp.
  - inversion H. inversion H0. econstructor. omega.
  - inversion H0.  econstructor.
  - pose proof (Nat.lt_ge_cases i0 i).
    destruct H1.
    + erewrite nth_error_compute_inst_None in H0; auto. 
      inversion H0.
    + apply Nat.lt_eq_cases in H1.
      destruct H1.
      * erewrite nth_error_compute_inst_Some in H0; auto.
        inversion H0. inversion H.
        subst.
        econstructor.
        omega.
      * subst.
        rewrite nth_error_compute_inst_None' in H0.
        inversion H0.
  - inversion H.
    subst.
    cases (apply_inst_subst (compute_inst_subst x i) sigma1).
    cases (apply_inst_subst (compute_inst_subst x i) sigma2).
    inversion H0.
    econstructor; eauto. 
    inversion H0.
    inversion H0.
Qed.

Hint Resolve new_tv_schm_to_new_tv_ty.

Lemma new_tv_s_id : forall (st st' : id) (s : substitution),
    new_tv_subst s st -> st' < st -> new_tv_ty (apply_subst s (var st')) st.
Admitted.

Hint Resolve new_tv_s_id.

Lemma new_tv_s_ty : forall (st : id) (s : substitution) (tau : ty),
    new_tv_ty tau st -> new_tv_subst s st -> new_tv_ty (apply_subst s tau) st.
Admitted.

Hint Resolve new_tv_s_ty.

Lemma new_tv_var_id : forall st1 st2 : id, st1 < st2 -> new_tv_ty (var st1) st2.
Admitted.

Hint Resolve new_tv_var_id.

Lemma new_tv_ty_ids : forall (st : id) (tau : ty), new_tv_ty tau st ->
                                               forall x : id, in_list_id x (ids_ty tau) = true -> x < st.
Proof.
  induction tau; intros; simpl in *; mysimp; intuition.
  destruct (eq_id_dec i x); intuition. inversion H. omega.
  apply in_list_id_or_append_inversion in H0.
  destruct H0; inversion H; auto.
Qed.

Hint Resolve new_tv_ty_ids.

Lemma new_tv_compose_subst_ctx : forall (s s1 s2 : substitution) (st : id) (G : ctx),
       (forall x : id, x < st -> apply_subst s (var x) = apply_subst s2 (apply_subst s1 (var x))) ->
       new_tv_ctx G st -> apply_subst_ctx s G = apply_subst_ctx s2 (apply_subst_ctx s1 G).
Admitted.

Lemma new_tv_schm_plus : forall sigma st st', new_tv_schm sigma st -> new_tv_schm sigma (st + st').
Proof.
  induction sigma; intros; try econstructor; eauto.
  inversion H. subst. auto.
  inversion H. subst. eauto.
  Unshelve. apply x.
Qed.

Hint Resolve new_tv_schm_plus.

Lemma new_tv_ctx_plus : forall G st st', new_tv_ctx G st -> new_tv_ctx G (st + st').
Proof.
  induction G; intros; simpl in *; auto.
  destruct a.
  econstructor; auto.
  inversion H. subst;
  eauto.
  inversion H. subst;
  eauto.
Qed.

Hint Resolve new_tv_ctx_plus.

Lemma new_tv_ty_to_schm : forall tau st, new_tv_schm (ty_to_schm tau) st -> new_tv_ty tau st.
Proof.
  intros.
  induction tau; simpl in *; try inversion H; try econstructor; eauto.
Qed.

Hint Resolve new_tv_ty_to_schm.

Lemma new_tv_s_ctx : forall (st : id) (s : substitution) (G : ctx),
    new_tv_ctx G st -> new_tv_subst s st -> new_tv_ctx (apply_subst_ctx s G) st.
Admitted.

Hint Resolve new_tv_s_ctx.

Lemma new_tv_schm_Succ : forall sigma i, new_tv_schm sigma i -> new_tv_schm sigma (S i).
Proof.
  intros.
  induction sigma;
  inversion H; econstructor; auto.
Qed.

Hint Resolve new_tv_schm_Succ.

Lemma new_tv_ctx_Succ : forall G i, new_tv_ctx G i -> new_tv_ctx G (S i).
Proof.
  intros.
  induction H; econstructor; eauto.
Qed.

Hint Resolve new_tv_ctx_Succ.

Lemma new_tv_ctx_implies_new_tv_schm : forall (G : ctx) (sigma : schm) (st x : id),
    in_ctx x G = Some sigma -> new_tv_ctx G st -> new_tv_schm sigma st.
Proof.
  Admitted.

Hint Resolve new_tv_ctx_implies_new_tv_schm.

Lemma new_tv_ctx_trans : forall st st' G, new_tv_ctx G st -> st <= st' -> new_tv_ctx G st'.
Admitted.

Hint Resolve new_tv_ctx_trans.

Lemma new_tv_schm_trans : forall st st' G, new_tv_ctx G st -> st <= st' -> new_tv_ctx G st'.
Admitted.

Hint Resolve new_tv_schm_trans.

Lemma new_tv_subst_trans : forall (s : substitution) (i1 i2 : id),
  new_tv_subst s i1 -> i1 <= i2 -> new_tv_subst s i2.
Admitted.

Hint Resolve new_tv_subst_trans.

Lemma new_tv_ty_trans_le : forall (tau : ty) (st1 st2 : id), new_tv_ty tau st1 -> st1 <= st2 -> new_tv_ty tau st2.
Proof.
  intros.
  Admitted.

Hint Resolve new_tv_ty_trans_le.

Lemma new_tv_schm_apply_subst : forall i tau s sigma, new_tv_schm sigma i ->
                                                  apply_subst_schm ((i, tau) :: s) sigma = apply_subst_schm s sigma.
Proof.
  intros.
  induction sigma;
  mysimp.
  cases (find_subst s i0); eauto;
  try inversion H; omega.
  inversion H. subst.
  fequals; eauto.
Qed.
  
Hint Resolve new_tv_schm_apply_subst.

Lemma new_tv_ctx_apply_subst_ctx : forall st tau s G, new_tv_ctx G st -> apply_subst_ctx ((st, tau) :: s) G = apply_subst_ctx s G.
Proof.
  Admitted.

Hint Resolve new_tv_ctx_apply_subst_ctx.

Lemma add_subst_add_ctx : forall (G : ctx) (s : substitution) (x : id) (st : id) (tau : ty),
    new_tv_ctx G st -> apply_subst_ctx ((st, tau)::s) ((x, sc_var st)::G) =  (x, (ty_to_schm tau)) :: (apply_subst_ctx s G).
Proof.
  intros;
  mysimp.
  rewrite new_tv_ctx_apply_subst_ctx; auto.
Qed.
  
Hint Resolve add_subst_add_ctx.

Lemma new_tv_compose_subst_type : forall (s s1 s2 : substitution) (st : id) (t : ty),
 (forall i : id, i < st -> apply_subst s (var i) = apply_subst s2 (apply_subst s1 (var i))) ->
 new_tv_ty t st -> apply_subst s t = apply_subst s2 (apply_subst s1 t).
Admitted.

Hint Resolve new_tv_compose_subst_type.
Hint Rewrite new_tv_compose_subst_type : subst.

Lemma add_subst_new_tv_ty : forall (s : substitution) (st : id) (tau1 tau2 : ty),
    new_tv_ty tau1 st -> apply_subst ((st, tau2)::s) tau1 = apply_subst s tau1.
  Admitted.

Hint Resolve add_subst_new_tv_ty.
Hint Rewrite add_subst_new_tv_ty : subst.

Lemma new_tv_gen_ty: forall (t : ty) (G : ctx) (st : id), new_tv_ty t st -> new_tv_ctx G st -> new_tv_schm (gen_ty t G) st.
  Admitted.

Hint Resolve new_tv_gen_ty.