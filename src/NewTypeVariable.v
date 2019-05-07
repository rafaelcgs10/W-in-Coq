(** * The new type variable relations
      This file contains the defintions of new type variable for types [new_tv_ty],
      schemes [new_tv_schm], contexts [new_tv_ctx] and substitutions [new_tv_subst].
      Several lemmas about new type variables are necessary for the completeness proof
      of algorithm W.
    *)

Set Implicit Arguments.

Require Import SimpleTypes.
Require Import Gen.
Require Import Omega.
Require Import Schemes.
Require Import Context.
Require Import SubstSchm.
Require Import List.
Require Import MyLtacs.
Require Import Subst.
Require Import SubstSchm.
Require Import ListIds.
Require Import Context.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import LibTactics.

(** * New type variable definition for simple types *)

Inductive new_tv_ty : ty -> id -> Prop :=
| new_tv_con : forall i i' : id, new_tv_ty (con i') i
| new_tv_var : forall i i' : id, i < i' -> new_tv_ty (var i) i'
| new_tv_arrow : forall (tau tau' : ty) (i : id), new_tv_ty tau i ->
                                             new_tv_ty tau' i ->
                                             new_tv_ty (arrow tau tau') i.

Hint Constructors new_tv_ty.

(** ** Lemmas that are only about new type variables for simple types. *)

Lemma new_tv_var_id : forall st1 st2 : id, st1 < st2 -> new_tv_ty (var st1) st2.
Proof.
  intros.
  eauto.
Qed.

Hint Resolve new_tv_var_id.

Lemma new_tv_ty_ids : forall (st : id) (tau : ty),
    new_tv_ty tau st ->
    forall x : id, in_list_id x (ids_ty tau) = true -> x < st.
Proof.
  induction tau; intros; simpl in *; mysimp; intuition.
  destruct (eq_id_dec i x); intuition. inversion H. omega.
  apply in_list_id_or_append_inversion in H0.
  destruct H0; inversion H; auto.
Qed.

Hint Resolve new_tv_ty_ids.

Lemma add_subst_new_tv_ty : forall (s : substitution) (st : id) (tau1 tau2 : ty),
    new_tv_ty tau1 st -> apply_subst ((st, tau2)::s) tau1 = apply_subst s tau1.
Proof.
  induction s; crush. 
  rewrite apply_subst_nil.
  induction tau1; crush.
  inverts* H; intuition. 
  inverts* H.
  fequals; eauto.
  induction tau1; crush;
  inverts* H; intuition. 
  inverts* H.
  fequals; eauto.
Qed.

Hint Resolve add_subst_new_tv_ty.
Hint Rewrite add_subst_new_tv_ty:RE.

Lemma new_tv_ty_trans_le : forall (tau : ty) (st1 st2 : id),
    new_tv_ty tau st1 -> st1 <= st2 -> new_tv_ty tau st2.
Proof.
  induction tau; crush.
  inverts* H.
  econstructor. omega.
  inverts* H.
Qed.

Hint Resolve new_tv_ty_trans_le.

Lemma new_tv_compose_subst_type : forall (s s1 s2 : substitution) (st : id) (tau : ty),
    (forall i : id, i < st -> apply_subst s (var i) = apply_subst s2 (apply_subst s1 (var i))) ->
    new_tv_ty tau st -> apply_subst s tau = apply_subst s2 (apply_subst s1 tau).
  induction tau.
  - crush.
  - crush.
  - intros.
    simpl.
    inverts* H0.
    fequals; eauto.
Qed.

Hint Resolve new_tv_compose_subst_type.
Hint Rewrite new_tv_compose_subst_type:RE.

(** * New type variable definition for schemes *)

Inductive new_tv_schm : schm -> id -> Prop :=
| new_tv_sc_con : forall i i' : id, new_tv_schm (sc_con i') i
| new_tv_sc_var : forall i i' : id, i < i' -> new_tv_schm (sc_var i) i'
| new_tv_sc_gen : forall i i' : id, new_tv_schm (sc_gen i') i
| new_tv_sc_arrow : forall (tau tau' : schm) (i : id), new_tv_schm tau i ->
                                               new_tv_schm tau' i ->
                                               new_tv_schm (sc_arrow tau tau') i.

Hint Constructors new_tv_schm.

(** ** Lemmas that are only about new type variables for schemes (and simple types). *)

(** Relating new type variables for simple types and schemes through [ty_to_schm]. *)
Lemma new_tv_ty_to_schm : forall tau st,
    new_tv_schm (ty_to_schm tau) st <-> new_tv_ty tau st.
Proof.
  intros. split.
  induction tau; simpl in *; try inversion H; try econstructor; eauto.
  inverts* H.
  inverts* H.
  inverts* H.
  intros.
  induction tau; simpl in *; try inversion H; try econstructor; eauto.
Qed.

Hint Resolve new_tv_ty_to_schm.

Lemma new_tv_schm_to_new_tv_ty : forall sigma x x0 i,
    new_tv_schm sigma x ->
    apply_inst_subst (compute_inst_subst x i) sigma = Some x0 ->
    new_tv_ty x0 (x + i).
Proof.
  induction sigma; intros; simpl in *; mysimp.
  - inversion H. inversion H0. econstructor. omega.
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

Lemma new_tv_schm_plus : forall sigma st st', new_tv_schm sigma st -> new_tv_schm sigma (st + st').
Proof.
  induction sigma; intros; try econstructor; eauto.
  inversion H. subst. auto.
  inversion H. subst. eauto.
  Unshelve. apply x.
Qed.

Hint Resolve new_tv_schm_plus.

Lemma new_tv_schm_Succ : forall sigma i, new_tv_schm sigma i -> new_tv_schm sigma (S i).
Proof.
  intros.
  induction sigma;
  inversion H; econstructor; auto.
Qed.

Hint Resolve new_tv_schm_Succ.

Lemma new_tv_schm_trans : forall st st' sigma,
    new_tv_schm sigma st -> st <= st' -> new_tv_schm sigma st'.
Proof.
  induction sigma; crush.
  inversion H.
  econstructor; crush. 
  inverts* H.
Qed.

Hint Resolve new_tv_schm_trans.

Lemma new_tv_schm_apply_subst : forall i tau s sigma,
    new_tv_schm sigma i ->
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

(* Relating new_tv_ty to compute_subst*)
Lemma new_tv_schm_compute_inst_subst :
  forall (sigma : schm) (tau tau' : ty) (s : substitution) (p : nat) (st : id) (x : list ty),
    new_tv_schm sigma st -> max_gen_vars sigma <= p ->
    apply_inst_subst (compute_inst_subst st p) sigma = Some tau ->
    apply_inst_subst x (apply_subst_schm s sigma) = Some tau' ->
    tau' = apply_subst ((compute_subst st x) ++ s) tau.
Proof.
  induction sigma.
  - intros.
    inversion H. subst.
    simpl in H1. inversion H1.
    simpl in H2. fold (apply_subst s (var i)) in H2.
    rewrite apply_subst_inst_to_ty_to_schm in H2.
    inversion H2.
    rewrite find_subst_some_apply_app_compute_subst; eauto.
   - crush. 
   - intros. 
     simpl in *.
     rewrite nth_error_compute_inst_Some in *; eauto.
     inversion H1. inversion H. subst.
     cases (nth_error x i).
     inversion H2. subst. clear H2 H1.
     erewrite find_subst_some_apply_app; eauto.
     rewrite Nat.add_comm.
     eapply find_subst_id_compute; eauto.
     inversion H2.
   - intros. 
     inversion H. subst.
     simpl in H0. rewrite apply_subst_schm_arrow in H2.
     edestruct (exist_arrow_apply_inst_arrow (compute_inst_subst st p)); eauto.
     destruct H3.
     edestruct (exist_arrow_apply_inst_arrow x); eauto.
     destruct H4. subst.
     apply and_arrow_apply_inst_arrow in H1.
     destruct H1.
     apply and_arrow_apply_inst_arrow in H2.
     destruct H2.
     simpl.
     eapply Nat.max_lub_r in H0 as H0r.
     eapply Nat.max_lub_l in H0 as H0l.
     erewrite <- IHsigma1; eauto.
     erewrite <- IHsigma2; eauto.
Qed.

Hint Resolve new_tv_schm_compute_inst_subst.

(** * New type variable definition for contexts *)

Inductive new_tv_ctx : ctx -> id -> Prop :=
| new_tv_ctx_nil : forall i : id, new_tv_ctx nil i
| new_tv_ctx_cons : forall (G : ctx) (i x : id) (sigma : schm),
    new_tv_ctx G i ->
    new_tv_schm sigma i ->
    new_tv_ctx ((x, sigma) :: G) i.

Hint Constructors new_tv_ctx.

(** ** Lemmas that are only about new type variables for contexts (and simple types and schemes). *)

Lemma new_tv_compose_subst_ctx : forall (s s1 s2 : substitution) (st : id) (G : ctx),
    (forall x : id, x < st -> apply_subst s (var x) = apply_subst s2 (apply_subst s1 (var x))) ->
    new_tv_ctx G st -> apply_subst_ctx s G = apply_subst_ctx s2 (apply_subst_ctx s1 G).
Proof.
  induction G. crush.
  intros.
  destruct a.
  inverts* H0.
  rename s0 into sigma.
  induction sigma.
  - inverts* H6.
    apply H in H1 as H1'.
    assert (apply_subst_ctx s ((i, sc_var i0) :: G) =
            ((i, ty_to_schm (apply_subst s (var i0)))::(apply_subst_ctx s G)) ).
    { reflexivity. }       
    rewrite H0.
    erewrite IHG; eauto.
    erewrite H; eauto.
    assert (apply_subst_ctx s2 (apply_subst_ctx s1 ((i, sc_var i0) :: G)) =
            ((i, (apply_subst_schm s2
               (apply_subst_schm s1 (sc_var i0))))::(apply_subst_ctx s2 (apply_subst_ctx s1 G))) ).
    { reflexivity. }
    rewrite H2.
    assert ((apply_subst_schm s1 (sc_var i0)) =
            ty_to_schm (apply_subst s1 (var i0))).
    { reflexivity. }
    rewrite H3.
    rewrite ty_to_subst_schm.
    reflexivity.
  - crush.
  - crush.
  - inverts* H6.
    simpl.
    fequals; eauto.
    fequals; eauto.
    fequals; eauto.
    apply IHsigma1 in H2.
    repeat rewrite <- apply_subst_ctx_eq in H2.
    inversion H2; eauto.
    apply IHsigma2 in H4.
    repeat rewrite <- apply_subst_ctx_eq in H4.
    inversion H4; eauto.
Qed.

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


Lemma new_tv_ctx_Succ : forall G i, new_tv_ctx G i -> new_tv_ctx G (S i).
Proof.
  intros.
  induction H; econstructor; eauto.
Qed.

Hint Resolve new_tv_ctx_Succ.

Lemma new_tv_ctx_implies_new_tv_schm : forall (G : ctx) (sigma : schm) (st x : id),
    in_ctx x G = Some sigma -> new_tv_ctx G st -> new_tv_schm sigma st.
Proof.
  induction G; crush.
  inverts* H0.
  inverts* H0.
Qed.

Hint Resolve new_tv_ctx_implies_new_tv_schm.

Lemma new_tv_ctx_trans : forall st st' G, new_tv_ctx G st -> st <= st' -> new_tv_ctx G st'.
Proof.
  induction G; crush.
  apply Nat.lt_eq_cases in H0.
  destruct H0; crush.
  inverts* H.
  apply Nat.lt_le_incl in H0.
  econstructor; eauto.
Qed.

Hint Resolve new_tv_ctx_trans.

Lemma new_tv_ctx_apply_subst_ctx : forall st tau s G,
    new_tv_ctx G st -> apply_subst_ctx ((st, tau) :: s) G = apply_subst_ctx s G.
Proof.
  induction G; crush.
  inverts* H.
  rewrite IHG; eauto.
  fequals.
  fequals.
  eauto.
Qed.

Hint Resolve new_tv_ctx_apply_subst_ctx.

Lemma add_subst_add_ctx : forall (G : ctx) (s : substitution) (x : id) (st : id) (tau : ty),
    new_tv_ctx G st ->
    apply_subst_ctx ((st, tau)::s) ((x, sc_var st)::G) =
    (x, (ty_to_schm tau)) :: (apply_subst_ctx s G).
Proof.
  intros;
  mysimp.
  rewrite new_tv_ctx_apply_subst_ctx; auto.
Qed.
  
Hint Resolve add_subst_add_ctx.

Lemma new_tv_ctx_inversion : forall G tau st i,
    new_tv_ctx ((i, tau) :: G) st ->
    new_tv_ctx G st.
Proof.
  induction G; crush.
  inverts* H.
Qed.

Hint Resolve new_tv_ctx_inversion.

Lemma new_tv_gen_aux_ty: forall (tau : ty) (G : ctx) (st : id) l,
    new_tv_ty tau st -> new_tv_ctx G st -> new_tv_schm (fst (gen_ty_aux tau G l)) st.
Proof.
  induction tau; crush.
  cases (in_list_id i (FV_ctx G)); crush.
  cases (index_list_id i l); crush.
  inverts* H.
  eapply IHtau1 with (G:= G) (l:=l) in H3; eauto.
  cases (gen_ty_aux tau1 G l); crush.
  eapply IHtau2 with (G:= G) (l:=l0) in H5; eauto.
  cases (gen_ty_aux tau2 G l0); crush.
Qed.

Hint Resolve new_tv_gen_aux_ty.

Lemma new_tv_gen_ty: forall (tau : ty) (G : ctx) (st : id),
    new_tv_ty tau st -> new_tv_ctx G st -> new_tv_schm (gen_ty tau G) st.
Proof.
  induction tau; unfold gen_ty; crush.
Qed. 

Hint Resolve new_tv_gen_ty.

(** * New type variable definition for substitutions *)

Inductive new_tv_subst : substitution -> id -> Prop :=
| new_tv_subst_intro : forall (i : id) (s : substitution),
                  (forall x : id, in_list_id x (FV_subst s) = true -> x < i) ->
                  new_tv_subst s i.

Hint Constructors new_tv_subst.

(** ** Lemmas that are only about new type variables for substitutions
       (and simple types and schemes and contexts). *)

Lemma arrowcons (A:Type) : forall (s1 s2:list A) x, s1 ++ x::s2 = (s1 ++ x::nil) ++ s2.
  intros ; rewrite app_ass ; auto.
Qed.

(** A hard lemma about adding a new element to a substitution. *)
Lemma new_ty_to_cons_new_tv_subst : forall tau i a s,
    a < i -> new_tv_ty tau i -> new_tv_subst s i -> new_tv_subst ((a, tau) :: s) i.
Proof.
  induction tau; intros; simpl in *. 
  inversion H0. subst.
  inversion H1.
  econstructor. intros.
  subst.
  simpl in H6. 
  destruct (eq_id_dec a x). subst.
  assumption.
  simpl in H6. 
  apply in_list_id_append_comm_true in H6.
  unfold img_ids in H6. simpl in H6. destruct (eq_id_dec i x).
  subst. assumption. fold (img_ids s) in H6.
  apply in_list_id_append_comm_true in H6.
  fold (FV_subst s) in H6. auto.
  econstructor. intros.
  simpl in H2.
  destruct (eq_id_dec a x). subst.
  assumption.
  apply in_list_id_append_comm_true in H2.
  unfold img_ids in H2. simpl in H2. 
  fold (img_ids s) in H2.
  apply in_list_id_append_comm_true in H2.
  fold (FV_subst s) in H2. 
  inversion H1. auto.
  inversion H0. subst.
  econstructor. intros.
  crush.
  apply in_list_id_append_comm_true in H2.
  unfold img_ids in H2. simpl in H2. 
  fold (img_ids s) in H2.
  assert (new_tv_subst ((a, tau1) :: s) i). auto.
  assert (new_tv_subst ((a, tau2) :: s) i). auto.
  inversion H3. subst.
  inversion H5. subst.
  specialize H7 with (x:=x).
  specialize H8 with (x:=x).
  simpl in *. destruct (eq_id_dec a x); eauto.
  unfold img_ids in *. simpl in *.
  fold (img_ids s) in *.
  apply in_list_id_append_comm_true in H2.
  rewrite <- app_assoc in H2.
  rewrite app_assoc in H2.
  apply in_list_id_append_comm_true2 in H2.
  rewrite app_assoc in H2.
  apply in_list_id_or_append_inversion in H2.
  destruct H2.
  rewrite <- app_assoc in H2.
  auto.
  auto.
Qed.

Hint Resolve new_ty_to_cons_new_tv_subst.

Lemma new_tv_subst_tail : forall a tau s i,
    new_tv_subst ((a, tau) :: s) i -> new_tv_subst s i.
Proof.
  intros.
  econstructor. intros.
  inverts* H. apply H1.
  unfold FV_subst in *.
  unfold img_ids in *.
  specialize H1 with (x:=x).
  induction tau.
  simpl in *. destruct (eq_id_dec a x). eauto.
  rewrite arrowcons.
  rewrite <- app_assoc.
  apply in_list_id_append_comm_true3.
  simpl. destruct (eq_id_dec i0 x); eauto.
  crush.
  crush.
Qed.

Hint Resolve new_tv_subst_tail.

Lemma new_tv_subst_arrow_inversion : forall a tau1 tau2 s i,
    new_tv_subst ((a, arrow tau1 tau2) :: s) i ->
    new_tv_subst ((a, tau1)::s) i /\ new_tv_subst ((a, tau2)::s) i.
Proof.
  intros.
  inverts* H.
  split.
  - econstructor.
    intros. apply H0. 
    unfold FV_subst in *.
    unfold img_ids in *.
    simpl (concat (map ids_ty (img ((a, arrow tau1 tau2) :: s)))).
    simpl (dom ((a, arrow tau1 tau2) :: s)).
    simpl (dom ((a, tau1) :: s)) in H.
    simpl (concat (map ids_ty (img ((a, tau1) :: s)))) in H.
    rewrite <- app_assoc.
    apply in_list_id_append_comm_true3 in H.
    apply in_list_id_append_comm_true3.
    apply in_list_id_or_append_inversion in H.
    destruct H.
    apply in_list_id_append1; eauto.
    apply in_list_id_append2; eauto.
  - econstructor.
    intros. apply H0. 
    unfold FV_subst in *.
    unfold img_ids in *.
    simpl (concat (map ids_ty (img ((a, arrow tau1 tau2) :: s)))).
    simpl (dom ((a, arrow tau1 tau2) :: s)).
    simpl (dom ((a, tau2) :: s)) in H.
    simpl (concat (map ids_ty (img ((a, tau2) :: s)))) in H.
    apply in_list_id_append_comm_true3 in H.
    apply in_list_id_append_comm_true3.
    apply in_list_id_or_append_inversion in H.
    destruct H.
    apply in_list_id_append1; eauto.
    apply in_list_id_append2; eauto.
Qed.

Hint Resolve new_tv_subst_arrow_inversion.
    
Lemma new_tv_subst_cons_new_tv_ty : forall tau s i a,
    new_tv_subst ((a, tau) :: s) i -> new_tv_ty tau i.
Proof.
  induction tau; crush.
  econstructor.
  inversion H. subst.
  apply H0. 
  unfold FV_subst.
  unfold img_ids.
  eapply in_list_id_append_comm_true.
  crush.
  apply new_tv_subst_arrow_inversion in H as H'.
  destruct H'.
  eauto.
Qed.

Hint Resolve new_tv_subst_cons_new_tv_ty.

Lemma new_tv_apply_subst_var : forall (st st' : id) (s : substitution),
    new_tv_subst s st -> st' < st -> new_tv_ty (apply_subst s (var st')) st.
Proof.
  induction s; crush.
Qed.

Hint Resolve new_tv_apply_subst_var.
 
Lemma new_tv_apply_subst_ty : forall (st : id) (s : substitution) (tau : ty),
    new_tv_ty tau st -> new_tv_subst s st -> new_tv_ty (apply_subst s tau) st.
Proof.
  induction tau; intros.
  inversion H; subst. eauto.
  inverts* H.
  crush.
  inverts* H.
  simpl.
  econstructor; eauto.
Qed.

Hint Resolve new_tv_apply_subst_ty.

Lemma new_tv_apply_subst_schm_var : forall  (s : substitution) (st st' : id),
    new_tv_subst s st -> st' < st -> new_tv_schm (apply_subst_schm s (sc_var st')) st.
Proof.
  intros.
  induction s. crush.
  destruct a.
  apply new_tv_subst_cons_new_tv_ty in H as H'.
  apply new_tv_subst_tail in H as H''.
  crush.
  apply new_tv_ty_to_schm.
  auto.
Qed.

Hint Resolve new_tv_apply_subst_schm_var.

Lemma new_tv_apply_subst_schm : forall (st : id) (s : substitution) (sigma : schm),
    new_tv_schm sigma st -> new_tv_subst s st -> new_tv_schm (apply_subst_schm s sigma) st.
Proof.
  induction sigma; intros.
  inverts* H.
  crush.
  simpl.
  auto.
  inverts* H.
  simpl.
  econstructor; eauto.
Qed.

Hint Resolve new_tv_apply_subst_schm.

Lemma new_tv_subst_list : forall (s1 s2 : substitution) (i : id),
    new_tv_subst s1 i ->
    new_tv_subst s2 i ->
    new_tv_subst (apply_subst_list s1 s2) i.
Proof.
  induction s1; crush.
  inversion H. subst.
  specialize H1 with (x:=a).
  simpl in H1.
  crush.
  apply new_ty_to_cons_new_tv_subst; eauto.
Qed.

Hint Resolve new_tv_subst_list.

Lemma new_tv_compose_subst : forall (s1 s2 : substitution) (i : id),
    new_tv_subst s1 i ->
    new_tv_subst s2 i ->
    new_tv_subst (compose_subst s1 s2) i.
Proof.
  induction s1, s2; crush.
  inversion H. inversion H0. subst.
  unfold compose_subst.
  econstructor.
  intros.
  unfold FV_subst in *.
  repeat rewrite dom_dist in H2.
  repeat rewrite img_ids_dist in H2.
  repeat rewrite apply_subst_list_dom in H2.
  repeat rewrite app_assoc in H2.
  assert (in_list_id x (img_ids ((p, t) :: s2) ++ (dom ((p, t) :: s2)) ++
          ((dom ((a, t0) :: s1) ++ img_ids (apply_subst_list ((a, t0) :: s1) ((p, t) :: s2))))) = true).
  { rewrite app_assoc. apply in_list_id_append_comm_true3.
    rewrite <- app_assoc. rewrite app_assoc. apply in_list_id_append_comm_true3.
    rewrite <- app_assoc. apply in_list_id_append_comm_true3.
    rewrite app_assoc. apply in_list_id_append_comm_true2.
    rewrite app_assoc. auto. }
  apply in_list_id_append_comm_true3 in H3.
  rewrite app_assoc in H3.
  apply in_list_id_or_append_inversion in H3.
  destruct H3.
  auto.
  pose proof (new_tv_subst_list  H H0).
  inversion H5. subst.
  unfold FV_subst in H6.
  repeat rewrite apply_subst_list_dom in H6.
  auto.
Qed.

Hint Resolve new_tv_compose_subst.

Lemma new_tv_subst_nil : forall st, new_tv_subst nil st.
Proof.
  intros. econstructor; intros ; simpl in *; inversion H.
Qed.

Hint Resolve new_tv_subst_nil.

Lemma new_tv_s_ctx : forall (st : id) (s : substitution) (G : ctx),
    new_tv_ctx G st -> new_tv_subst s st -> new_tv_ctx (apply_subst_ctx s G) st.
Proof.
  induction G; crush.
  inverts* H.
Qed.

Hint Resolve new_tv_s_ctx.

Lemma new_tv_subst_trans : forall (s : substitution) (i1 i2 : id),
  new_tv_subst s i1 -> i1 <= i2 -> new_tv_subst s i2.
Proof.
  induction s; crush.
  inverts* H.
  econstructor.
  intros.
  specialize H1 with (x:=x).
  assert (x < i1).
  { auto. }
  omega.
Qed.

Hint Resolve new_tv_subst_trans.

Lemma new_tv_subst_false : forall st s t, new_tv_subst ((st, t) :: s) st -> False.
Proof.
  intros.
  induction s. inversion H.
  specialize H0 with (x:=st).
  simpl in H0.
  destruct (eq_id_dec st st);
  intuition.
  inversion H.
  simpl in H0.
  specialize H0 with (x:=st).
  destruct (eq_id_dec st st); intuition.
Qed.

Hint Resolve new_tv_subst_false.
