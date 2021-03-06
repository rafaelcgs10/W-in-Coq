(** * The generalization functions and lemmas
      This file contains the defintion of the generalization function [gen_ty].
      The generalization process is essential in the let case of algorithm W.
    *)

Require Import LibTactics.
Require Import Sublist.
Require Import Context.
Require Import ListIds.
Require Import Schemes.
Require Import SubstSchm.
Require Import Rename.
Require Import Disjoints.
Require Import Arith.Arith_base.
Require Import List.
Require Import SimpleTypes.
Require Import Subst.
Require Import MyLtacs.

(** * Generalization of non-free variables in a type *)

Fixpoint gen_ty_aux (tau : ty) (G : ctx) (l : list id) : schm * list id :=
  match tau with
  | var i => if in_list_id i (FV_ctx G) then (sc_var i, l) else
              match index_list_id i l with
              | None => (sc_gen (List.length l), (l ++ i::nil))
              | Some j => (sc_gen j, l)
              end
  | con i => (sc_con i, l)
  | arrow tau' tau'' => match gen_ty_aux tau' G l with
                       | (sc_tau, l') => match gen_ty_aux tau'' G l' with
                                        | (sc_tau', l'') =>
                                          (sc_arrow sc_tau  sc_tau', l'')
                                        end
                       end
  end.

Definition gen_ty (tau : ty) (G : ctx) :=
  @fst schm (list id) (gen_ty_aux tau G nil).

(** List of variables that can be generalized. *)
Fixpoint gen_ty_vars (tau : ty) (G : ctx) :=
  match tau with
  | con i => nil
  | var i => if in_list_id i (FV_ctx G) then nil else (i::nil)
  | arrow tau' tau'' => (gen_ty_vars tau' G) ++ (gen_ty_vars tau'' G)
  end.

(** * Several lemmas about the generalization function *)

(** gen_ty_vars distributes over arrow. *)
Lemma gen_ty_vars_arrow : forall t1 t2 G, gen_ty_vars (arrow t1 t2) G =
                                     gen_ty_vars t1 G ++ gen_ty_vars t2 G.
Proof.
  intros.
  reflexivity.
Qed.

Hint Resolve gen_ty_vars_arrow:core.
Hint Rewrite gen_ty_vars_arrow:RE.

Lemma fst_gen_aux_arrow_rewrite : forall (tau tau' : ty) (G : ctx) (l : list id),
    fst (gen_ty_aux (arrow tau tau') G l) = sc_arrow (fst (gen_ty_aux tau G l))
                                            (fst (gen_ty_aux tau' G (snd (gen_ty_aux tau G l)))).
Proof.
  intros; crush.
  destruct (gen_ty_aux tau G l); crush.
  destruct (gen_ty_aux tau' G l0 ); crush.
Qed.

Hint Resolve fst_gen_aux_arrow_rewrite:core.
Hint Rewrite fst_gen_aux_arrow_rewrite:RE.


(** snd gen_ty_aux distributes over arrow *)
Lemma snd_gen_ty_aux_arrow_rewrite : forall (tau tau': ty) (G : ctx) (l: list id),
    (snd (gen_ty_aux (arrow tau tau') G l)) =
    (snd (gen_ty_aux tau' G (snd (gen_ty_aux tau G l)))).
Proof.
  intros.
  cases (gen_ty_aux tau G l). simpl. rewrite Eq.
  cases (gen_ty_aux tau' G l0). reflexivity.
Qed.

Hint Resolve snd_gen_ty_aux_arrow_rewrite:core.
Hint Rewrite snd_gen_ty_aux_arrow_rewrite:RE.

Lemma free_and_bound_are_disjoints : forall (G : ctx) (tau: ty),
    (are_disjoints (gen_ty_vars tau G ) (FV_ctx G)).
Proof.
  intros.
  unfold are_disjoints.
  intros.
  induction tau.
  - simpl in *.
    cases (in_list_id i (FV_ctx G)).
    simpl in H.
    inversion H.
    simpl in H.
    cases (eq_id_dec i x).
    subst. assumption.
    inversion H.
  - simpl in *.
    inversion H.
  - simpl in H.
    apply in_list_id_or_append_inversion in H.
    destruct H.
    apply IHtau1.
    assumption.
    apply IHtau2.
    assumption.
Qed.

Hint Resolve free_and_bound_are_disjoints:core.

(** ** Lemmas related to the renaminng substitution *)

Lemma is_subst_list_gen_vars_aux : forall (rho: ren_subst) (G: ctx) (t: ty),
    (is_rename_subst rho) ->
    (are_disjoints (dom_ren rho) (FV_ctx G)) ->
    (are_disjoints (FV_ctx G) (img_ren rho)) ->
    (is_sublist_id (gen_ty_vars t G) (dom_ren rho)) ->
    (is_sublist_id (gen_ty_vars (apply_subst (rename_to_subst rho) t) G)
                       (img_ren rho)).
  induction t.
  - intros; simpl in *.
    cases (in_list_id i (FV_ctx G)).
    + fold (apply_subst (rename_to_subst rho) (var i)).
      rewrite <- (dom_rename_to_subst) in *.
      erewrite apply_subst_dom_false.
      simpl. destruct (in_list_id i (FV_ctx G)); try contradiction.
      apply nil_is_sublist.
      inversion Eq.
      eapply disjoint_inversion2. apply H0. 
      mysimp.
    + inversion H2. inversion H. subst.
      specialize H3 with (st:=i).
      simpl in H3. destruct (eq_id_dec i i); intuition.
      fold (apply_subst (rename_to_subst rho) (var i)).
      rewrite apply_subst_rename_to_subst; auto.
      simpl.
      assert (in_list_id (apply_ren_subst rho i) (FV_ctx G) = false).
      { eapply disjoint_inversion2. apply H1. apply in_list_id_dom_img; auto. }
      rewrite H3. econstructor.
      intros. simpl in H5. destruct (eq_id_dec (apply_ren_subst rho i) st).
      rewrite <- e0. apply in_list_id_dom_img. auto. intuition.
  - intros. rewrite apply_subst_con. simpl. apply nil_is_sublist.
  - intros. rewrite apply_subst_arrow in *. simpl. simpl in H2.
    apply append_sublist.
    + eapply IHt1; auto. eapply sublist_of_append_inversion1.
      apply H2.
    + eapply IHt2; auto. eapply sublist_of_append_inversion2.
      apply H2.
Qed.

Hint Resolve is_subst_list_gen_vars_aux:core.

Lemma is_sublist_gen_vars : forall (rho : ren_subst) (s: substitution) (G : ctx) (tau: ty),
    (is_rename_subst rho) -> (dom_ren rho) = (gen_ty_vars tau G) ->
    (are_disjoints (FV_ctx G) (img_ren rho)) ->
    (is_sublist_id (gen_ty_vars (apply_subst (rename_to_subst rho) tau) G)
                       (img_ren rho)).
Proof.
  intros.
  inversion H.
  eapply is_subst_list_gen_vars_aux; auto.
  rewrite H0.
  eapply free_and_bound_are_disjoints. rewrite <- H0.
  apply sublist_reflexivity.
Qed.

Hint Resolve is_sublist_gen_vars:core.

(** The generalizable ids form a sublist of dom rho, for some conditions *)
Lemma is_sublist_gen_ty_dom_rho: forall (G : ctx) (rho : ren_subst) (tau: ty) (l : list id),
    (is_rename_subst rho) ->
    (are_disjoints (dom_ren rho) (FV_ctx G)) -> (are_disjoints (FV_ctx G) (img_ren rho)) ->
    (is_sublist_id l (dom_ren rho)) -> (is_sublist_id (gen_ty_vars tau G) (dom_ren rho)) ->
    (is_sublist_id  (snd (gen_ty_aux tau G l)) (dom_ren rho)).
Proof.
  induction tau; intros.
  - simpl.
    cases (in_list_id i (FV_ctx G)).
    + simpl. auto.
    + cases (index_list_id i l).
      * simpl. auto.
      * simpl.
        inversion H3. subst.
        apply sublist_cons_inv; auto.
        apply H4; auto. 
        simpl. 
        destruct (in_list_id i (FV_ctx G)); intuition.
        mysimp.
  - simpl. auto.
  - generalize dependent l.
    intros.
    erewrite snd_gen_ty_aux_arrow_rewrite.
    eapply IHtau2; auto.
    eapply IHtau1; auto.
    rewrite gen_ty_vars_arrow in H3.
    eapply sublist_of_append_inversion1.
    apply H3.
    eapply sublist_of_append_inversion2.
    apply H3.
Qed.        

Hint Resolve is_sublist_gen_ty_dom_rho:core.

Lemma renaming_not_concerned_with_gen_vars: forall (rho : ren_subst) (s: substitution) (G : ctx) (tau: ty),
    (renaming_of_not_concerned_with rho (gen_ty_vars tau G) (FV_ctx G) (FV_subst s)) ->
    (are_disjoints (FV_subst s) (gen_ty_vars (apply_subst (rename_to_subst rho) tau) G)).
Proof.
  intros.
  inversion H.
  inversion H0.
  unfold FV_subst in *.
  apply disjoint_list_and_append.
  - eapply disjoint_sublist_bis.
    apply are_disjoints_symetry in H3.
    apply disjoint_list_and_append_inversion1 in H3.
    apply H3.
    eapply is_sublist_gen_vars; auto.
  - eapply disjoint_sublist_bis.
    apply are_disjoints_symetry in H3.
    apply disjoint_list_and_append_inversion2 in H3.
    apply H3.
    eapply is_sublist_gen_vars; auto.
Qed.

Hint Resolve renaming_not_concerned_with_gen_vars:core.

(** This lemma is used to prove gen_ty_renaming, which says that gen_ty
    works that same for a special renaming *)
Lemma gen_ty_renaming_aux: forall (tau : ty) (G: ctx) (rho : ren_subst) l,
    (is_rename_subst rho) ->
    (are_disjoints  (dom_ren rho) (FV_ctx G)) ->
    (is_sublist_id (gen_ty_vars tau G) (dom_ren rho)) ->
    (is_sublist_id l (dom_ren rho)) ->
    (are_disjoints  (FV_ctx G) (img_ren rho)) ->
    (gen_ty_aux (apply_subst (rename_to_subst rho) tau) G 
                (List.map (apply_ren_subst rho) l)) = 
    ((fst  (gen_ty_aux tau G l)), (List.map (apply_ren_subst rho) (snd (gen_ty_aux tau G l)))).
Proof.
  induction tau.
  - do 3 intro.
    simpl.
    cases (in_list_id i (FV_ctx G)).
    + intros.
      assert (in_list_id i (dom_ren rho) = false).
      {erewrite disjoint_inversion2. reflexivity.  apply H0. auto. }
      fold (apply_subst (rename_to_subst rho) (var i)).
      rewrite apply_subst_dom_false; auto.
      simpl.
      destruct (in_list_id i (FV_ctx G)); intuition.
      rewrite dom_rename_to_subst.
      auto.
    + intros.
      inversion H.
      repeat fold (apply_subst (rename_to_subst rho) (var i)).
      rewrite apply_subst_rename_to_subst; auto.
      simpl.
      inversion H1.
      simpl in H4.
      specialize H7 with (st:=i).
      simpl in H7.
      cases (eq_id_dec i i); intuition.
      subst.
      rewrite rename_img; auto.
      erewrite <- index_rename; auto.
      cases (index_list_id i l).
      reflexivity.
      repeat rewrite map_length.
      simpl.
      fequals; eauto.
      rewrite map_app.
      reflexivity.
  - intros.
    simpl.
    reflexivity.
  - intros.
    inversion H1.
    inversion H2.
    subst.
    rewrite apply_subst_arrow.
    simpl.
    rewrite IHtau1; auto.
    cases (gen_ty_aux tau1 G l).
    rewrite IHtau2; auto.
    cases (gen_ty_aux tau2 G l0).
    simpl.
    rewrite Eq0.
    simpl. reflexivity.
    rewrite gen_ty_vars_arrow in H1.
    apply sublist_of_append_inversion2 in H1.
    auto.
    rewrite gen_ty_vars_arrow in H1.
    apply sublist_of_append_inversion1 in H1.
    rewrite <- Eq.
    eapply is_sublist_gen_ty_dom_rho; auto.
    rewrite gen_ty_vars_arrow in H1.
    apply sublist_of_append_inversion1 in H1.
    auto.
Qed.

Hint Resolve gen_ty_renaming_aux:core.

(** gen_ty works that same for a special renaming *)
Lemma gen_ty_renaming: forall (G : ctx) (rho : ren_subst) (tau : ty) (s: substitution),
    (renaming_of_not_concerned_with rho (gen_ty_vars tau G) (FV_ctx G) (FV_subst s))
    -> (gen_ty tau G) = (gen_ty (apply_subst (rename_to_subst rho) tau) G).
Proof.
  intros.
  inversion H.
  unfold gen_ty in *.
  assert (nil = (List.map (apply_ren_subst rho) nil)).
  { reflexivity. }
  rewrite H8 at 2.
  subst.
  rewrite gen_ty_renaming_aux; auto.
  rewrite H1.
  apply free_and_bound_are_disjoints.
  rewrite <- H1.
  auto.
Qed.

Hint Resolve gen_ty_renaming:core.
Hint Rewrite gen_ty_renaming:RE.

Lemma gen_apply_rename_to_subst : forall (G : ctx) (rho : ren_subst) (tau : ty),
    is_rename_subst rho -> dom_ren rho = gen_ty_vars tau G ->
    are_disjoints (FV_ctx G) (img_ren rho) ->
    gen_ty tau G = gen_ty (apply_subst (rename_to_subst rho) tau) G.
Proof.
  intros; unfold gen_ty in |- *.
  inversion H.
  assert (nil = map (apply_ren_subst rho) nil).
  {reflexivity. }
  rewrite H5.
  rewrite gen_ty_renaming_aux; auto.
  rewrite H0.
  apply free_and_bound_are_disjoints.
  rewrite <- H0.
  apply sublist_reflexivity.
Qed.

Hint Resolve gen_apply_rename_to_subst:core.
Hint Rewrite gen_apply_rename_to_subst:RE.

(** ** Several other generalization lemmas *)

(** If the ids of a ty are free in the G, then gen_ty_aux is just ty_to_schm *)
Lemma is_not_generalizable : forall (G : ctx)  (tau : ty) (l: list id),
    is_sublist_id (ids_ty tau) (FV_ctx G) -> gen_ty_aux tau G l= (ty_to_schm tau, l).
Proof.
  induction tau; intros; auto; simpl;
    inversion H.
  - rewrite H0; auto. mysimp.
  - erewrite IHtau1.
    erewrite IHtau2. reflexivity.
    simpl in H.
    apply sublist_of_append_inversion2 in H. auto.
    apply sublist_of_append_inversion1 in H. auto.
Qed.

Hint Resolve is_not_generalizable:core.
Hint Rewrite is_not_generalizable:RE.

Lemma gen_ty_aux_in_subst_ctx : forall (tau: ty) (G : ctx) (s : substitution) (l : list id),
    (are_disjoints (dom s) (gen_ty_vars tau G)) ->
    (are_disjoints (img_ids s) (gen_ty_vars tau G)) ->
    (gen_ty_aux (apply_subst s tau) (apply_subst_ctx s G) l) = 
    ((apply_subst_schm s (fst (gen_ty_aux tau G l))), 
     (snd (gen_ty_aux tau G l))).
Proof.
  induction tau; intros.
  - simpl in *.
    cases (in_list_id i (FV_ctx G)).
    + fold (apply_subst s (var i)).
      rewrite is_not_generalizable.
      rewrite <- ty_to_subst_schm.
      reflexivity.
      eapply sublist_FV_ctx; auto.
    + repeat fold (apply_subst s (var i)).
      erewrite apply_subst_dom_false.
      simpl.
      rewrite not_in_FV_ctx; auto.
      cases (index_list_id i l);
        simpl; eauto.
      apply are_disjoints_symetry in H0. 
      unfold are_disjoints in H0.
      specialize H0 with (x:=i).
      apply H0. mysimp.
      apply are_disjoints_symetry in H. 
      unfold are_disjoints in H.
      specialize H with (x:=i).
      apply H. mysimp.
  - rewrite apply_subst_con.
    simpl. reflexivity.
  - rewrite apply_subst_arrow. simpl.
    erewrite IHtau1; auto.
    erewrite IHtau2; auto.
    cases (gen_ty_aux tau1 G l).
    cases (gen_ty_aux tau2 G l0).
    simpl. 
    fequals.
    fequals.
    rewrite Eq0. reflexivity.
    rewrite Eq0. reflexivity.
    simpl in H. apply disjoint_list_and_append_inversion2 in H. auto.
    simpl in H0. apply disjoint_list_and_append_inversion2 in H0. auto.
    simpl in H. apply disjoint_list_and_append_inversion1 in H. auto.
    simpl in H0. apply disjoint_list_and_append_inversion1 in H0. auto.
Qed.

Hint Resolve gen_ty_aux_in_subst_ctx:core.
Hint Rewrite gen_ty_aux_in_subst_ctx:RE.

Lemma gen_ty_in_subst_ctx : forall (G : ctx) (s : substitution) (tau : ty),
    (are_disjoints (FV_subst s) (gen_ty_vars tau G)) ->
    (apply_subst_schm s (gen_ty tau G)) =
    (gen_ty (apply_subst s tau) (apply_subst_ctx s G)).
Proof.
  intros.
  unfold gen_ty. unfold FV_subst in H.
  erewrite gen_ty_aux_in_subst_ctx; auto;
    apply are_disjoints_symetry in H;
    apply are_disjoints_symetry.
  apply disjoint_list_and_append_inversion1 in H.
  auto.
  apply disjoint_list_and_append_inversion2 in H.
  auto.
Qed.

Hint Resolve gen_ty_in_subst_ctx:core.
Hint Rewrite gen_ty_in_subst_ctx:RE.

Lemma exists_snd_gen_aux_app : forall (G : ctx) (tau : ty) (l : list id),
    exists l', snd (gen_ty_aux tau G l) = l ++ l' /\ are_disjoints (FV_ctx G) l'.
Proof.
  induction tau.
  - intro. simpl.
    cases (in_list_id i (FV_ctx G)).
    exists (nil : list id).
    crush.
    cases (index_list_id i l).
    exists (nil : list id).
    crush.
    exists (i::nil : list id).
    crush.
  - crush.
    exists (nil : list id).
    crush.
  - intros.
    rewrite snd_gen_ty_aux_arrow_rewrite.
    edestruct IHtau1.
    destruct H.
    rewrite H.
    edestruct IHtau2.
    destruct H1.
    rewrite H1.
    exists (x ++ x0).
    split.
    rewrite app_assoc. reflexivity.
    eauto.
Qed.

Hint Resolve exists_snd_gen_aux_app:core.

Lemma disjoint_snd_gen_aux : forall (G : ctx) (l : list id) (tau : ty),
    are_disjoints (FV_ctx G) l -> are_disjoints (FV_ctx G) (snd (gen_ty_aux tau G l)).
Proof.
  intros.
  destruct (exists_snd_gen_aux_app G tau l).
  destruct H0. rewrite H0.
  eauto.
Qed.

Hint Resolve disjoint_snd_gen_aux:core.

Lemma length_snd_gen_aux : forall (G : ctx) (tau : ty) (l : list id),
    length (snd (gen_ty_aux tau G l)) = max (length l) (max_gen_vars (fst (gen_ty_aux tau G l))).
Proof.
  induction tau; crush.
  cases (in_list_id i (FV_ctx G)); crush.
  rewrite Nat.max_0_r. reflexivity.
  cases (index_list_id i l).
  simpl.
  symmetry.
  apply max_l.
  change (i0 < length l) in |- *.
  eapply index_lt; eauto.
  simpl.
  rewrite app_length.
  simpl.
  symmetry.
  assert (S (length l) = length l + 1). auto with *.
  rewrite H.
  apply max_r. auto with *.
  rewrite Nat.max_0_r. reflexivity.
  cases (gen_ty_aux tau1 G l).
  cases (gen_ty_aux tau2 G l0).
  simpl.
  specialize IHtau1 with (l:=l).
  rewrite Eq in IHtau1.
  specialize IHtau2 with (l:=l0).
  rewrite Eq0 in IHtau2.
  simpl in *.
  rewrite IHtau1 in IHtau2.
  rewrite Nat.max_assoc.
  assumption.
Qed.
