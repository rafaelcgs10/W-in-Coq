(** * The more general relations
      This file contains the defintions of more general schemes [more_general] and more 
      contexts [more_general_ctx].
      Several lemmas about the two relations are necessary for the let case in the
      completeness proof of algorithm W.
    *)

Set Implicit Arguments.

Require Import Omega.
Require Import Schemes.
Require Import SubstSchm.
Require Import Gen.
Require Import List.
Require Import Sublist.
Require Import ListIds.
Require Import Context.
Require Import Typing.
Require Import Disjoints.
Require Import NewTypeVariable.
Require Import SimpleTypes.
Require Import Subst.
Require Import MyLtacs.
Require Import NthErrorTools.
Require Import ProductList.
Require Import DisjointTail.
Require Import LibTactics.

Inductive more_general : schm -> schm -> Prop :=
| more_general_intro : forall sigma1 sigma2 : schm,
    (forall tau : ty, is_schm_instance tau sigma2 -> is_schm_instance tau sigma1) ->
    more_general sigma1 sigma2.

Hint Constructors more_general.

(** ** More general schemes lemmas *)

Lemma more_general_in_list_FV_schm : forall sigma1 sigma2,
    more_general sigma1 sigma2 ->
    forall i, in_list_id i (FV_schm sigma1) = true ->
         in_list_id i (FV_schm sigma2) = true.
Proof.
  induction sigma1; eauto.
  - intros.
    induction sigma2; eauto.
    crush.
    inverts* H.
    specialize H1 with (tau:=var i1).
    edestruct H1.
    unfold is_schm_instance.
    exists (nil:inst_subst).
    reflexivity.
    simpl in *. inverts* H.
    crush.
    inverts* H.
    specialize H1 with (tau:=con i1).
    edestruct H1.
    exists (nil:inst_subst).
    simpl in *. reflexivity.
    simpl in *. inverts* H.
    inverts* H.
    specialize H1 with (tau:=var i1).
    simpl in *. crush.
    edestruct H1.
Abort.

Lemma sc_var_more_general_than_sigma : forall (sigma : schm) (st : id),
    more_general (sc_var st) sigma -> sigma = sc_var st.
Proof.
  intros.
  inversion H. subst.
  cut (is_schm_instance (find_instance sigma (con 0)) sigma); eauto.
  intros.
  cut (is_schm_instance (find_instance sigma (con 0)) (sc_var st)); eauto.
  intros.
  inversion_clear H2.
  destruct sigma; simpl in *.
  inverts* H3.
  inverts* H3.
  inverts* H3.
  inverts* H3.
Qed.  

Hint Resolve sc_var_more_general_than_sigma.
Hint Rewrite sc_var_more_general_than_sigma:RE.

Lemma more_general_arrow_inversion1 : forall sigma1 sigma2 sigma1' sigma2' : schm,
    more_general (sc_arrow sigma1 sigma2) (sc_arrow sigma1' sigma2') ->
    more_general sigma1 sigma1'.
Proof.
  intros.
  inverts* H.
  econstructor.
  intros.
  inverts* H.
  destruct (apply_inst_subst_succeeds sigma2'
            (x ++ make_constant_inst_subst (max_gen_vars sigma2') (con 0))).
  rewrite app_length.
  rewrite length_make_constant_inst_subst.
  auto with *.
  cut (is_schm_instance (arrow tau x0) (sc_arrow sigma1 sigma2)).
  intros.
  inverts* H2.
  exists x1.
  apply exist_arrow_apply_inst_arrow2 in H3 as H3'.
  destruct H3' as [tau1 [tau2 H3']].
  destructs H3'.
  inverts* H5.
  apply H0.
  exists (x ++ make_constant_inst_subst (max_gen_vars sigma2') (con 0)).
  simpl.
  erewrite apply_inst_subst_ge_app; eauto.
  rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Hint Resolve more_general_arrow_inversion1.

Lemma more_general_arrow_inversion2 : forall sigma1 sigma2 sigma1' sigma2' : schm,
    more_general (sc_arrow sigma1 sigma2) (sc_arrow sigma1' sigma2') ->
    more_general sigma2 sigma2'.
Proof.
  intros.
  inverts* H.
  econstructor.
  intros.
  inverts* H.
  destruct (apply_inst_subst_succeeds sigma1'
            (x ++ make_constant_inst_subst (max_gen_vars sigma1') (con 0))).
  rewrite app_length.
  rewrite length_make_constant_inst_subst.
  auto with *.
  cut (is_schm_instance (arrow x0 tau) (sc_arrow sigma1 sigma2)).
  intros.
  inverts* H2.
  exists x1.
  apply exist_arrow_apply_inst_arrow2 in H3 as H3'.
  destruct H3' as [tau1 [tau2 H3']].
  destructs H3'.
  inversion H5. 
  rewrite H7 in *.
  rewrite H8 in *.
  apply H4.
  apply H0.
  exists (x ++ make_constant_inst_subst (max_gen_vars sigma1') (con 0)).
  simpl.
  erewrite apply_inst_subst_ge_app with (sigma:=sigma2'); eauto.
  rewrite H.
  rewrite H1.
  reflexivity.
Qed.

Hint Resolve more_general_arrow_inversion2.

Lemma FV_more_general : forall sigma1 sigma2 : schm,
    more_general sigma1 sigma2 ->
    is_sublist_id (FV_schm sigma1) (FV_schm sigma2).
Proof.
  induction sigma1; crush.
  apply sc_var_more_general_than_sigma in H.
  subst. auto.
  inverts* H.
  apply arrow_sigma_more_general_than_arrow in H0 as H0'.
  destruct H0'.
  subst.
  simpl.
  eapply sublist_of_2_app; eauto.
Qed.

Hint Resolve FV_more_general.

(** ** More general contexts lemmas *)

Inductive more_general_ctx : ctx -> ctx -> Prop :=
| more_general_ctx_nil : more_general_ctx nil nil
| more_general_ctx_cons : forall (G1 G2 : ctx) (i : id) (sigma1 sigma2 : schm),
    more_general_ctx G1 G2 -> more_general sigma1 sigma2 ->
    more_general_ctx ((i, sigma1) :: G1) ((i, sigma2) :: G2).

Hint Constructors more_general_ctx.

Lemma FV_more_general_ctx : forall G1 G2 : ctx,
    more_general_ctx G1 G2 ->
    Sublist.is_sublist_id (FV_ctx G1) (FV_ctx G2).
Proof.
  intros.
  induction H.
  - eauto.
  - simpl.
    unfold FV_ctx.
    simpl.
    fold (FV_ctx G1).
    fold (FV_ctx G2).
    eapply sublist_of_2_app;
    eauto.
Qed.

Hint Resolve FV_more_general_ctx.

(** This complex lemma is needed to prove [more_general_ctx_disjoint_prefix_apply_inst]. *)
Lemma inst_subst_to_subst_aux :
  forall (G : ctx) (tau1 tau2 : ty) (l L : list id)
    (is_s : list ty) (phi : substitution),
    are_disjoints (FV_ctx G) l ->
    apply_inst_subst is_s (fst (gen_ty_aux tau1 G l)) = Some tau2 ->
    is_disjoint_with_some_tail (FV_ctx G) (snd (gen_ty_aux tau1 G l)) L ->
    product_list L is_s = Some phi -> apply_subst phi tau1 = tau2.
Proof.
  induction tau1.
  - do 7 intro; simpl in |- *.
    cases (in_list_id i (FV_ctx G)).
    + intros.
      simpl in *.
      rewrite Eq in H0. simpl in H0.
      inverts* H0.
      fold (apply_subst phi (var i)).
      apply apply_subst_dom_false.
      rewrite (@domain_product L is_s phi); auto.
      inverts* H1.
      destruct H0.
      destruct a.
      subst.
      eauto.
    + simpl in H0.
      cases (index_list_id i l).
      intros.
      rewrite Eq in H0.
      simpl in H0.
      fold (apply_subst phi (var i)).
      cases (nth_error is_s i0).
      {  
        simpl in * |-.
        inverts* H0.
        eapply (@image_by_product2 L is_s i i0); eauto.
        inverts* H1.
        destruct H0.
        destruct a.
        subst.
        auto. }
      { inverts* H0. }
      * rewrite Eq in H0.
        simpl in H0.
        cases (nth_error is_s (length l)).
        { simpl in *.
          intros.
          fold (apply_subst phi (var i)).
          eapply (@image_by_product2 L is_s i (length l)); eauto.
          inverts* H1.
          destruct H3.
          destruct a.
          subst.
          apply index_list_id_app; eauto.
          inverts* H0.
        }
        { inverts* H0. }
  - crush.
  - intros.
    rewrite fst_gen_aux_arrow_rewrite in H0.
    apply exist_arrow_apply_inst_arrow2 in H0.
    destruct H0 as [tau1 [tau3 H0]].
    destructs H0.
    subst.
    simpl.
    rewrite snd_gen_ty_aux_arrow_rewrite in H1.
    erewrite (@IHtau1_2 tau3 (snd (gen_ty_aux tau1_1 G l)) L is_s phi); eauto.
    erewrite (@IHtau1_1 tau1 l L is_s phi); eauto.
Qed.

Hint Resolve inst_subst_to_subst_aux.
Hint Rewrite inst_subst_to_subst_aux:RE.

(** This huge lemma is needed to prove [more_general_gen_ty]. *)
Lemma more_general_ctx_disjoint_prefix_apply_inst :
  forall (G1 G2 : ctx) (tau1 tau2 : ty) (phi : substitution)
    (l2 l1 L P : list id) (is_s : inst_subst),
    more_general_ctx G1 G2 -> are_disjoints (FV_ctx G2) l2 ->
    are_disjoints (FV_ctx G1) l1 ->
    apply_inst_subst is_s (fst (gen_ty_aux tau1 G2 l2)) = Some tau2 ->
    is_disjoint_with_some_tail (FV_ctx G2) (snd (gen_ty_aux tau1 G2 l2)) L ->
    product_list L is_s = Some phi ->
    is_disjoint_with_some_tail (FV_ctx G1) (snd (gen_ty_aux tau1 G1 l1)) P ->
    apply_inst_subst (map_apply_subst_over_list_ty (ty_from_id_list P) phi)
                     (fst (gen_ty_aux tau1 G1 l1)) = Some tau2.
Proof.
  simple induction tau1.
  - do 8 intro; intros more_gen_hyp disjoint1 disjoint2.
    simpl. 
    cases (in_list_id i (FV_ctx G1)).
    erewrite (Sublist.sublist_inv1 i (FV_more_general_ctx more_gen_hyp)); eauto.
    cases (index_list_id i l1).
    + simpl.
      intros.
      inverts* H2.
      destruct H3.
      destruct a.
      rewrite H2.
      rewrite (ty_from_id_list_app l1 x).
      rewrite (map_extend_app phi (ty_from_id_list l1) (ty_from_id_list x)).
      rewrite (nth_error_app (map_apply_subst_over_list_ty
               (ty_from_id_list l1) phi) (map_apply_subst_over_list_ty (ty_from_id_list x) phi)).
      erewrite (@nth_error_map phi (ty_from_id_list l1) i0 (var i)).
      rewrite (@inst_subst_to_subst_aux G2 (var i) tau2 l2 L is_s phi); eauto.
      eauto.
      crush.
    + intros.
      inverts* H2.
      destruct H3.
      destruct a.
      rename x into P2.
      simpl in *.
      rewrite H2.
      rewrite (ty_from_id_list_app (l1 ++ i::nil) P2).
      rewrite (map_extend_app phi (ty_from_id_list (l1 ++ i::nil)) (ty_from_id_list P2)).
      rewrite (nth_error_app (map_apply_subst_over_list_ty (ty_from_id_list (l1 ++ i::nil)) phi)
                             (map_apply_subst_over_list_ty (ty_from_id_list P2) phi)).
      erewrite (@nth_error_map phi (ty_from_id_list (l1 ++ i::nil)) (length l1) (var i)).
      erewrite (@inst_subst_to_subst_aux G2 (var i) tau2 l2 L is_s phi); eauto.
      rewrite ty_from_id_list_app; simpl.
      rewrite <- length_ty_from_id_list; eauto.
      crush.
  - crush. 
  - do 11 intro; intros more_gen_hyp disjoint1 disjoint2.
    rewrite fst_gen_aux_arrow_rewrite; intro.
    destruct (@exist_arrow_apply_inst_arrow2  
                (fst (gen_ty_aux t G2 l2)) (fst (gen_ty_aux t0 G2 (snd (gen_ty_aux t G2 l2))))
                tau2 is_s H1).
    intros.
    destruct H2.
    destructs H2.
    rewrite <- H7.
    rewrite snd_gen_ty_aux_arrow_rewrite in *.
    repeat rewrite fst_gen_aux_arrow_rewrite.
    simpl.
    rewrite (@H x phi l2 l1 L P is_s); eauto.
    rewrite (@H0 x0 phi (snd (@gen_ty_aux t G2 l2)) (snd (@gen_ty_aux t G1 l1)) L P is_s); eauto.
Qed.

Hint Resolve more_general_ctx_disjoint_prefix_apply_inst.

Lemma more_general_gen_ty : forall (G1 G2 : ctx) (t : ty),
    more_general_ctx G1 G2 -> more_general (gen_ty t G1) (gen_ty t G2).
Proof.
  intros.
  econstructor. intros.
  inverts* H0.
  unfold gen_ty in |- *; intros.
  destruct (product_list_exists t G2 x); eauto.
  unfold is_schm_instance.
  exists (map_apply_subst_over_list_ty (ty_from_id_list (snd (gen_ty_aux t G1 nil))) x0).
  rewrite (@more_general_ctx_disjoint_prefix_apply_inst G1 G2 t tau x0 nil nil
    (snd (gen_ty_aux t G2 nil)) (snd (gen_ty_aux t G1 nil)) x)
 ; eauto.
Qed.

Hint Resolve more_general_gen_ty.

Lemma typing_pat_in_a_more_general_ctx : forall (p : pat) (G2 G1 : ctx) (t : ty),
    more_general_ctx G1 G2 -> has_type_pat G2 p t -> has_type_pat G1 p t.
Proof.
  induction p.
  - induction G2.
    + intros.
      inverts* H0. crush.
    +  destruct a.
       intros.
       inversion_clear H.
       destruct (eq_id_dec i0 i).
       *
       subst.
       inversion_clear H0.
       apply var_htp with (sigma:=sigma1); eauto.
       crush.
       simpl in H. destruct (eq_id_dec i i); intuition.
       inverts* H.
       inverts* H2.
       * apply has_type_pat_var_ctx_diff. eauto.
       eapply IHG2; eauto.
       inverts* H0.
       econstructor; crush.
  - intros.
    inverts* H0.
    econstructor; eauto.
Qed.

Hint Resolve typing_pat_in_a_more_general_ctx.

Lemma typing_patterns_in_a_more_general_ctx : forall (l : non_empty_list pat) (G2 G1 : ctx) (t : ty),
    more_general_ctx G1 G2 -> has_type_patterns G2 l t -> has_type_patterns G1 l t.
Proof.
  induction l.
  - intros.
    econstructor.
    eapply typing_pat_in_a_more_general_ctx.
    apply H.
    inverts* H0.
  - intros.
    econstructor.
    inverts* H0.
    inverts* H0.
Qed.

Hint Resolve typing_patterns_in_a_more_general_ctx.

Lemma typing_in_a_more_general_ctx : forall (e : term) (G2 G1 : ctx) (t : ty),
    more_general_ctx G1 G2 -> has_type G2 e t -> has_type G1 e t.
Proof.
  intros.
  apply (has_type_mut
         (fun (G' : ctx) (e' : term) (t' : ty) (h : has_type G' e' t') => forall t G2 G1,
                       more_general_ctx G1 G2 -> has_type G2 e' t -> has_type G1 e' t)
         (fun  (G' : ctx) (l' : non_empty_list term) (t' : ty) (h : has_type_terms G' l' t') => forall t G2 G1,
                       more_general_ctx G1 G2 -> has_type_terms G2 l' t -> has_type_terms G1 l' t)
         ) with (c:=G2) (t0:=t) (t:=e) (G2:=G2); auto.
  (** const case *)
  - intros.
    inverts* H2.
    econstructor.
  - induction G0.
    + intros.
      inverts* H2.
      crush.
    + destruct a.
      intros.
      inversion_clear H1.
      rename i into i', x into i.
      destruct (eq_id_dec i0 i).
      * subst.
        inversion_clear H2.
        apply var_ht with (sigma:=sigma1); eauto.
        crush.
        simpl in H1.
        destruct (eq_id_dec i i); intuition.
        inverts* H1.
        inverts* H4.
      * apply has_type_var_ctx_diff; eauto.
        eapply IHG0; eauto.
        inverts* H2.
        econstructor; crush.
  (** lambda case *)
  - intros.
    inverts* H3.
    econstructor; eauto.
    eapply H1; eauto.
    econstructor; eauto.
  (** app case *)
  - intros.
    inverts* H4.
    econstructor; eauto.
  (** let case *)
  - intros.
    inverts* H4.
    econstructor.
    eapply H1; eauto.
    eapply H2; eauto.
    auto.
  (** case case *)
  - intros.
    induction cs.
    + inverts* H4.
      econstructor;
      eauto.
    + inverts* H4.
      econstructor; eauto.
  (** terms one case *)
  - intros.
    inverts* H3.
    econstructor; eauto.
  (** terms many case *)
  - intros.
    inverts* H4.
    econstructor; eauto.
Qed.
    
Hint Resolve typing_in_a_more_general_ctx.

Lemma more_general_ctx_refl : forall G : ctx, more_general_ctx G G.
Proof.
  simple induction G; auto.
  intros; elim a; auto.
Qed.

Hint Resolve more_general_ctx_refl.

(** Auxiliary lemma for the [more_general_gen_ty_before_apply_subst] lemma *)
Lemma more_general_gen_ty_before_apply_subst_aux :
  forall (G : ctx) (tau1 tau2 : ty) (phi s : substitution) (l1 l2 L P : list id) (is_s : inst_subst),
    are_disjoints (FV_ctx G) l1 ->
    are_disjoints (FV_ctx (apply_subst_ctx s G)) l2 ->
    apply_inst_subst is_s (fst (gen_ty_aux (apply_subst s tau1)
                                           (apply_subst_ctx s G) l2)) = Some tau2 ->
    is_disjoint_with_some_tail (FV_ctx (apply_subst_ctx s G))
                     (snd (gen_ty_aux (apply_subst s tau1) (apply_subst_ctx s G) l2)) L ->
    product_list L is_s = Some phi ->
    is_disjoint_with_some_tail (FV_ctx G) (snd (gen_ty_aux tau1 G l1)) P ->
    apply_inst_subst (map_apply_subst_over_list_ty (ty_from_id_list P) (compose_subst s phi))
                     (apply_subst_schm s (fst (gen_ty_aux tau1 G l1))) = Some tau2.
Proof.
  induction tau1.
  - do 8 intro; simpl in |- *.
    intros disjoint1 disjoint2.
    repeat fold (apply_subst s (var i)) in *.
    cases (in_list_id i (FV_ctx G)).
    + simpl.
      repeat fold (apply_subst s (var i)) in *.
      erewrite is_not_generalizable; eauto.
      crush.
    + do 3 intro.
      cases (index_list_id i l1).
      * intros. inverts* H2. destruct H3.
        simpl.
        destruct a. subst.
        rewrite ty_from_id_list_app.
        rewrite map_extend_app; eauto.
        rewrite nth_error_app; eauto.
        erewrite nth_error_map; eauto.
        rewrite apply_compose_equiv.
        erewrite inst_subst_to_subst_aux.
        reflexivity.
        apply disjoint2.
        eauto.
        eauto.
        eauto.
        rewrite length_map.
        rewrite length_ty_from_id_list.
        eauto.
      * intros.
        inverts* H2.
        destruct H3. destruct a.
        subst.
        rewrite ty_from_id_list_app; eauto.
        rewrite map_extend_app; eauto.
        simpl.
        rewrite nth_error_app; eauto.
        erewrite nth_error_map; eauto.
        rewrite apply_compose_equiv.
        erewrite inst_subst_to_subst_aux with (l := l2); eauto.
        rewrite length_map2.
        eauto.
  - crush.
  - do 8 intro; intros disjoint1 disjoint2.
    rewrite apply_subst_arrow.
    rewrite fst_gen_aux_arrow_rewrite.
    intro.
    apply exist_arrow_apply_inst_arrow2 in H as H'.
    destruct H' as [tau1 [tau3 H3]].
    destructs H3.
    subst.
    repeat rewrite snd_gen_ty_aux_arrow_rewrite.
    intros prex prod.
    rewrite fst_gen_aux_arrow_rewrite.
    rewrite apply_subst_schm_arrow.
    intros.
    simpl.
    erewrite (@IHtau1_1 tau1 phi s l1 l2 L P is_s); eauto.
    erewrite (@IHtau1_2 tau3 phi s) with
        (l2:= (snd (gen_ty_aux (apply_subst s tau1_1) (apply_subst_ctx s G) l2))); eauto.
Qed.

Hint Resolve more_general_gen_ty_before_apply_subst_aux.

Lemma more_general_gen_ty_before_apply_subst : forall (s : substitution) (G : ctx) (tau : ty),
 more_general (apply_subst_schm s (gen_ty tau G)) (gen_ty (apply_subst s tau) (apply_subst_ctx s G)).
Proof.
  intros.
  econstructor.
  intros.
  inverts* H.
  unfold gen_ty in *.
  destruct (product_list_exists (apply_subst s tau) (apply_subst_ctx s G) x); eauto.
  unfold is_schm_instance.
  exists (map_apply_subst_over_list_ty (ty_from_id_list (snd (gen_ty_aux tau G nil))) (compose_subst s x0)).
  eauto.
Qed.

Hint Resolve more_general_gen_ty_before_apply_subst.
