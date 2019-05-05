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

Require Import LibTactics.

Inductive more_general : schm -> schm -> Prop :=
| more_general_intro : forall sigma1 sigma2 : schm,
    (forall tau : ty, is_schm_instance tau sigma2 -> is_schm_instance tau sigma1) ->
    more_general sigma1 sigma2.

Hint Constructors more_general.

Inductive more_general_ctx : ctx -> ctx -> Prop :=
| more_general_ctx_nil : more_general_ctx nil nil
| more_general_ctx_cons : forall (G1 G2 : ctx) (i : id) (sigma1 sigma2 : schm),
    more_general_ctx G1 G2 -> more_general sigma1 sigma2 ->
    more_general_ctx ((i, sigma1) :: G1) ((i, sigma2) :: G2).

Hint Constructors more_general_ctx.

Fixpoint product_list (l1 : list id) (l2 : list ty) :=
  match l1 with
  | nil =>  Some nil
  | st :: l'1 => match l2 with
                | nil => None
                | t :: l'2 => match product_list l'1 l'2 with
                             | None => None
                             | Some s => Some ((st, t) :: s)
                             end
                end
  end.

Fixpoint ty_from_id_list (l : list id) : list ty :=
  match l with
  | nil => nil
  | x::l' => var x :: ty_from_id_list l'
  end.

Lemma ty_from_id_list_app : forall l1 l2 : list id,
    ty_from_id_list (l1 ++ l2) = ty_from_id_list l1 ++ ty_from_id_list l2.
Proof.
  induction l1; crush.
Qed.

Hint Resolve ty_from_id_list_app.
Hint Rewrite ty_from_id_list_app:RE.

Fixpoint map_extend_subst_type (l : list ty) (s2 : substitution) :=
  match l with
  | nil => nil
  | t::l' => apply_subst s2 t :: map_extend_subst_type l' s2
  end.

Lemma map_extend_app : forall (s : substitution) (l1 l2 : list ty),
    map_extend_subst_type (l1 ++ l2) s = map_extend_subst_type l1 s ++ map_extend_subst_type l2 s.
Proof.
  induction l1; crush.
Qed.

Hint Resolve map_extend_app.
Hint Rewrite map_extend_app:RE.

Inductive is_prefixe_free2 : list id -> list id -> list id -> Prop :=
|  prefixe_free2_intro : forall C l L : list id,
    {l1 : list id | L = l ++ l1 /\ are_disjoints C l1} -> is_prefixe_free2 C l L.

Hint Constructors is_prefixe_free2.

Lemma more_general_in_list_FV_schm : forall sigma1 sigma2, more_general sigma1 sigma2 ->
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

Fixpoint find_instance (sigma : schm) (tau : ty) :=
  match sigma with
  | sc_con i => con i
  | sc_var i => var i
  | sc_gen st => tau
  | sc_arrow sigma1 sigma2 => arrow (find_instance sigma1 tau) (find_instance sigma2 tau)
  end.

Fixpoint make_constant_inst_subst (n : id) (tau : ty)  :=
  match n with
  | O => nil 
  | S p => tau :: make_constant_inst_subst p tau
  end.
Lemma nth_error_make_constant_inst_subst3 : forall (p n : id) (tau : ty),
    S n <= p -> nth_error (make_constant_inst_subst p tau) n = Some tau.
Proof.
  induction p; crush.
  destruct n; crush.
  apply IHp.
  auto with *.
Qed.

Hint Resolve nth_error_make_constant_inst_subst3.
Hint Rewrite nth_error_make_constant_inst_subst3:RE.

Lemma apply_subst_inst_make_constant_inst_subst : forall (sigma : schm) (tau : ty) (p : id),
    max_gen_vars sigma <= p ->
    apply_inst_subst (make_constant_inst_subst p tau) sigma = Some (find_instance sigma tau).
Proof.
  induction sigma; eauto.
  unfold max_gen_vars.
  unfold apply_inst_subst.
  intros tau p le.
  simpl in le.
  crush.
  intros tau p le.
  simpl.
  erewrite (IHsigma1 tau p); eauto.
  erewrite (IHsigma2 tau p); eauto.
  eauto with *.
  simpl in le.
  pose proof (PeanoNat.Nat.le_max_l (max_gen_vars sigma1) (max_gen_vars sigma2)).
  auto with *.
Qed.

Hint Resolve apply_subst_inst_make_constant_inst_subst.
Hint Resolve apply_subst_inst_make_constant_inst_subst:RE.

Lemma find_some_instance_of_some_sigma : forall (sigma : schm) (tau : ty),
    is_schm_instance (find_instance sigma tau) sigma.
Proof.
  intros.
  unfold is_schm_instance.
  exists (make_constant_inst_subst (max_gen_vars sigma) tau).
  auto.
Qed.

Hint Resolve find_some_instance_of_some_sigma.
Hint Rewrite find_some_instance_of_some_sigma:RE.

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

Lemma var_is_not_instance_of_arrow : forall (sigma1 sigma2 : schm) (i : id),
    ~ is_schm_instance (var i) (sc_arrow sigma1 sigma2).
Proof.
  intros. intro.
  inverts* H.
  apply exist_arrow_apply_inst_arrow2 in H0.
  destruct H0 as [tau1 [tau2 H]].
  destruct H.
  destruct H0.
  inverts* H1.
Qed.

Hint Resolve var_is_not_instance_of_arrow.

Lemma con_is_not_instance_of_arrow : forall (sigma1 sigma2 : schm) (i : id),
    ~ is_schm_instance (con i) (sc_arrow sigma1 sigma2).
Proof.
  intros. intro.
  inverts* H.
  apply exist_arrow_apply_inst_arrow2 in H0.
  destruct H0 as [tau1 [tau2 H]].
  destruct H.
  destruct H0.
  inverts* H1.
Qed.

Hint Resolve con_is_not_instance_of_arrow.

Lemma arrow_sigma_more_general_than_arrow : forall sigma sigma1 sigma2 : schm,
    (forall tau : ty, is_schm_instance tau sigma -> is_schm_instance tau (sc_arrow sigma1 sigma2)) ->
    {sig_sig : schm * schm | sigma = sc_arrow (fst sig_sig) (snd sig_sig)}.
Proof.
  induction sigma. 
  - cut (is_schm_instance (find_instance (sc_var i) (con i)) (sc_var i)); auto.
    intros.
    cut (is_schm_instance (find_instance (sc_var i) (con i)) (sc_arrow sigma1 sigma2)); auto.
    intros.
    simpl in *.
    absurd (is_schm_instance (var i) (sc_arrow sigma1 sigma2)); auto.
  - intros.
    assert (is_schm_instance (con i) (sc_con i)).
    exists (nil:inst_subst). reflexivity.
    apply H in H0. 
    apply con_is_not_instance_of_arrow in H0.
    contradiction.
  - intros.
    cut (is_schm_instance (find_instance (sc_gen i) (con i)) (sc_gen i)); auto.
    intros.
    cut (is_schm_instance (find_instance (sc_gen i) (con i)) (sc_arrow sigma1 sigma2)); auto.
    intros.
    absurd (is_schm_instance (con i) (sc_arrow sigma1 sigma2)); auto.
  - intros.
    exists (sigma1, sigma2). reflexivity.
Qed.

Hint Resolve arrow_sigma_more_general_than_arrow.
Hint Resolve arrow_sigma_more_general_than_arrow:RE.

Lemma length_map : forall (s : substitution) (l : list ty),
    length (map_extend_subst_type l s) = length l.
Proof.
  induction l; crush.
Qed.

Hint Resolve length_map.
Hint Rewrite length_map:RE.

Lemma length_app : forall (A : Set) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1; crush.
Qed.
 
Hint Resolve length_app.

Lemma length_make_constant_inst_subst : forall (n : nat) (t : ty), length (make_constant_inst_subst n t) = n.
  induction n; crush.
Qed.

Hint Resolve length_make_constant_inst_subst.

Lemma apply_inst_subst_succeeds : forall (sigma : schm) (is_s : inst_subst),
    max_gen_vars sigma <= length is_s -> exists tau, apply_inst_subst is_s sigma = Some tau.
Proof.
  induction sigma; crush.
  cases (nth_error is_s i).
  exists t. reflexivity.
  apply nth_error_None in Eq.
  omega.
  edestruct IHsigma1; eauto.
  apply Nat.max_lub_l in H.
  apply H.
  edestruct IHsigma2; eauto.
  apply Nat.max_lub_r in H.
  apply H.
  rewrite H0.
  rewrite H1.
  exists (arrow x x0). reflexivity.
Qed.

Hint Resolve apply_inst_subst_succeeds.

Lemma apply_inst_subst_ge_app : forall (sigma : schm) (is_s l : inst_subst),
    max_gen_vars sigma <= length is_s -> apply_inst_subst (is_s ++ l) sigma = apply_inst_subst is_s sigma.
Proof.
  induction sigma; crush.
  cases (nth_error (is_s ++ l) i).
  erewrite <- nth_error_app1; eauto.
  rewrite Eq. reflexivity.
  erewrite <- nth_error_app1; eauto.
  rewrite Eq. reflexivity.
  erewrite IHsigma1; eauto.
  erewrite IHsigma2; eauto.
  apply Nat.max_lub_r in H.
  apply H.
  apply Nat.max_lub_l in H.
  apply H.
Qed.

Hint Resolve apply_inst_subst_ge_app.

Lemma is_instance_le_max : forall (sigma : schm) (tau : ty) (is_s : inst_subst),
    apply_inst_subst is_s sigma = Some tau -> max_gen_vars sigma <= length is_s.
Proof.
  induction sigma; crush.
  cases (nth_error is_s i).
  inverts* H.
  assert (nth_error is_s i <> None). { intro. rewrite Eq in H. inversion H. }
  apply nth_error_Some in H. omega.                                   
  inversion H.
  cases (apply_inst_subst is_s sigma1).
  cases (apply_inst_subst is_s sigma2).
  apply Nat.max_lub_iff; eauto.
  inversion H.
  inversion H.
Qed.

Hint Resolve is_instance_le_max.

Lemma more_general_arrow_inversion1 : forall sigma1 sigma2 sigma1' sigma2' : schm,
    more_general (sc_arrow sigma1 sigma2) (sc_arrow sigma1' sigma2') ->
    more_general sigma1 sigma1'.
Proof.
  intros.
  inverts* H.
  econstructor.
  intros.
  inverts* H.
  destruct (apply_inst_subst_succeeds sigma2' (x ++ make_constant_inst_subst (max_gen_vars sigma2') (con 0))).
  rewrite length_app.
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
  destruct (apply_inst_subst_succeeds sigma1' (x ++ make_constant_inst_subst (max_gen_vars sigma1') (con 0))).
  rewrite length_app.
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

Lemma FV_more_general : forall sigma1 sigma2 : schm, more_general sigma1 sigma2 ->
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
 
Lemma FV_more_general_ctx : forall G1 G2 : ctx, more_general_ctx G1 G2 ->
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

Lemma nth_error_app : forall (l l1 : list ty) (n : id), n < length l -> nth_error (l ++ l1) n = nth_error l n.
Proof.
  induction l; crush.
  induction n; crush.
  erewrite <- IHl; crush.
Qed.

Hint Resolve nth_error_app.
Hint Rewrite nth_error_app:RE.

Lemma domain_product : forall (l : list id) (is_s : inst_subst) (phi : substitution),
    product_list l is_s = Some phi -> dom phi = l.
Proof.
  induction l. crush.
  destruct is_s. crush.
  intros. 
  simpl in *.
  cases (product_list l is_s).
  inverts* H.
  simpl.
  erewrite IHl; eauto.
  inverts* H.
Qed.  

Lemma index_list_id_nil : forall st, index_list_id st nil = None.
Proof.
  induction st; crush.
Qed.

Hint Resolve index_list_id_nil.
Hint Rewrite index_list_id_nil:RE.

Lemma index_aux1 : forall st l k n, index_list_id_aux (S n) st l = Some k -> index_list_id_aux n st l = Some (Nat.pred k).
Proof.
  induction l. crush.
  intros.
  simpl in *.
  destruct (eq_id_dec a st).
  subst.
  inversion H. subst. reflexivity.
  apply IHl in H. auto.
Qed.

Hint Resolve index_aux1.

Lemma index_aux2 : forall st l k n, index_list_id_aux n st l = Some k -> index_list_id_aux (S n) st l = Some (S k).
Proof.
  induction l; crush.
Qed.

Hint Resolve index_aux2.

Lemma index_aux_false : forall l n m i, m < n -> index_list_id_aux n i l = Some m -> False.
Proof.
  induction l; crush.
  Unshelve.
  auto.
  auto.
Qed.
Hint Resolve index_aux_false.

Lemma image_by_product2 : forall (l : list id) (is_s : inst_subst) (st : id) 
                            (n0 : id) (phi : substitution) (tau : ty),
    index_list_id st l = Some n0 ->
    product_list l is_s = Some phi ->
    nth_error is_s n0 = Some tau -> apply_subst phi (var st) = tau.
Proof.
  induction l; unfold index_list_id. crush.
  intros.
  simpl in *.
  destruct (eq_id_dec a st).
  inverts* H.
  destruct is_s.
  inversion H0.
  subst.
  simpl in H1. inverts* H1.
  cases (product_list l is_s).
  inverts* H0.
  crush.
  inversion H0.
  destruct is_s.
  inversion H0.
  cases (product_list l is_s).
  inverts* H0.
  crush.
  eapply IHl.
  apply index_aux1 in H.
  unfold index_list_id. apply H.
  apply Eq.
  destruct n0. simpl in *.
  inverts* H1. destruct is_s.
  assert (False). { eapply index_aux_false with (n := 1) (m := 0); eauto. } contradiction.
  assert (False). { eapply index_aux_false with (n := 1) (m := 0); eauto. } contradiction.
  simpl. eauto.
  inversion H0.
Qed.

Hint Resolve image_by_product2.

Lemma index_lt : forall (l : list id) (st : id) (k : id),
    index_list_id st l = Some k -> k < length l.
Proof.
  induction l. unfold index_list_id in *. crush.
  unfold index_list_id in *.
  intros.
  simpl in H.
  destruct (eq_id_dec a st).
  inversion H. subst.
  simpl. auto with *.
  apply index_aux1 in H.
  apply IHl in H.
  simpl. omega.
Qed.

Hint Resolve index_lt.

Lemma index_list_none_any_k : forall l i k k', index_list_id_aux k i l = None -> index_list_id_aux k' i l = None.
Proof.
  induction l; crush.
Qed.

Hint Resolve index_list_none_any_k.

Lemma index_list_id_cons : forall (l : list id) (i : id),
    index_list_id i l = None -> index_list_id i (l ++ i::nil) = Some (length l).
Proof.
  induction l; unfold index_list_id in *; crush.
Qed.

Hint Resolve index_list_id_cons.

Lemma index_list_id_aux_app : forall (l1 l2 : list id) (n : id) (i : id) k,
 index_list_id_aux k i l1 = Some n -> index_list_id_aux k i (l1 ++ l2) = Some n.
Proof.
  induction l1; unfold index_list_id in *; crush.
Qed.

Hint Resolve index_list_id_aux_app.

Lemma index_list_id_app : forall (l1 l2 : list id) (n : id) (i : id),
 index_list_id i l1 = Some n -> index_list_id i (l1 ++ l2) = Some n.
Proof.
  induction l1; unfold index_list_id in *; crush.
Qed.

Hint Resolve index_list_id_app.

Lemma Snd_gen_aux_with_app3 : forall (G : ctx) (tau : ty) (l : list id),
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

Hint Resolve Snd_gen_aux_with_app3.

Lemma disjoint_Snd_gen_aux : forall (G : ctx) (l : list id) (tau : ty),
    are_disjoints (FV_ctx G) l -> are_disjoints (FV_ctx G) (snd (gen_ty_aux tau G l)).
Proof.
  intros.
  destruct (Snd_gen_aux_with_app3 G tau l).
  destruct H0. rewrite H0.
  eauto.
Qed.

Hint Resolve disjoint_Snd_gen_aux.

Lemma is_prefixe2_gen_aux : forall (l L : list id) (tau : ty) (G : ctx),
    is_prefixe_free2 (FV_ctx G) (snd (gen_ty_aux tau G l)) L ->
    is_prefixe_free2 (FV_ctx G) l L.
Proof.
  intros.
  destruct (Snd_gen_aux_with_app3 G tau l).
  destruct H0.
  inverts* H.
  destruct H2.
  destruct a.
  econstructor.
  exists (x ++ x0).
  split.
  rewrite app_assoc.
  rewrite <- H0.
  rewrite H. reflexivity.
  eauto.
Qed.

Hint Resolve is_prefixe2_gen_aux.

Lemma inst_subst_to_subst_aux_4 : forall (G : ctx) (tau1 tau2 : ty) (l L : list id)
                                   (is_s : list ty) (phi : substitution),
    are_disjoints (FV_ctx G) l ->
    apply_inst_subst is_s (fst (gen_ty_aux tau1 G l)) = Some tau2 ->
    is_prefixe_free2 (FV_ctx G) (snd (gen_ty_aux tau1 G l)) L ->
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
    
Hint Resolve inst_subst_to_subst_aux_4.
Hint Rewrite inst_subst_to_subst_aux_4:RE.

Lemma nth_error_map : forall (s : substitution) (x : list ty) (n : id) (tau : ty),
    nth_error x n = Some tau ->
    nth_error (map_extend_subst_type x s) n = Some (apply_subst s tau).
Proof.
  induction x; crush.
  rewrite nth_error_nil in H.
  inversion H.
  induction n; crush.
Qed.

Hint Resolve nth_error_map.
Hint Rewrite nth_error_map:RE.

Lemma nth_error_k_not_zero : forall a k l, k <> 0 -> nth_error ((var a)::l) k = nth_error l (pred k).
Proof.
  induction k; crush.
Qed.


Hint Resolve nth_error_k_not_zero.

Lemma index_list_id_nth : forall (l : list id) (k : id) (i : id),
    index_list_id i l = Some k -> nth_error (ty_from_id_list l) k = Some (var i).
Proof.
  induction l; unfold index_list_id in *. crush.
  intros.
  simpl in *. destruct (eq_id_dec a i).
  inverts* H. subst. reflexivity.
  erewrite nth_error_k_not_zero.
  apply IHl.
  apply index_aux1 in H.
  auto.
  destruct k.
  apply index_aux_false in H; auto. 
  auto. 
Qed.

Hint Resolve index_list_id_nth.
Hint Rewrite index_list_id_nth:RE.

Lemma length_ty_from_id_list : forall l : list id, length (ty_from_id_list l) = length l.
Proof.
  induction l; crush.
Qed.

Hint Resolve length_ty_from_id_list.
Hint Rewrite length_ty_from_id_list:RE.

Lemma nth_error_app_cons : forall (l : list ty) (tau : ty), nth_error (l ++ tau::nil) (length l) = Some tau.
simple induction l; auto.
Qed.

Hint Resolve nth_error_app_cons.

Lemma length_map2 : forall (s : substitution) (l : list id),
    length (map_extend_subst_type (ty_from_id_list l) s) = length l.
Proof.
  simple induction l; auto.
  intros; simpl in |- *.
  rewrite H; auto.
Qed.

Hint Resolve length_map2.
Hint Rewrite length_map2:RE.

Lemma length_app_cons : forall (A : Set) (l : list A) (x : A), length (l ++ x :: nil) = S (length l).
Proof.
  simple induction l; auto.
  intros; simpl in |- *; auto.
Qed.

Hint Resolve length_app_cons.
Hint Rewrite length_app_cons:RE.

Lemma more_general_gen_type_aux : forall (G1 G2 : ctx) (tau1 tau2 : ty) (phi : substitution)
                                    (l2 l1 L P : list id) (is_s : inst_subst),
    more_general_ctx G1 G2 -> are_disjoints (FV_ctx G2) l2 ->
    are_disjoints (FV_ctx G1) l1 ->
    apply_inst_subst is_s (fst (gen_ty_aux tau1 G2 l2)) = Some tau2 ->
    is_prefixe_free2 (FV_ctx G2) (snd (gen_ty_aux tau1 G2 l2)) L ->
    product_list L is_s = Some phi ->
    is_prefixe_free2 (FV_ctx G1) (snd (gen_ty_aux tau1 G1 l1)) P ->
    apply_inst_subst (map_extend_subst_type (ty_from_id_list P) phi)
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
     rewrite (nth_error_app (map_extend_subst_type (ty_from_id_list l1) phi) (map_extend_subst_type (ty_from_id_list x) phi)).
     erewrite (@nth_error_map phi (ty_from_id_list l1) i0 (var i)).
     rewrite (@inst_subst_to_subst_aux_4 G2 (var i) tau2 l2 L is_s phi); eauto.
     eauto.
     crush.
   +
     intros.
     inverts* H2.
     destruct H3.
     destruct a.
     rename x into P2.
     simpl in *.
     rewrite H2.
     rewrite (ty_from_id_list_app (l1 ++ i::nil) P2).
     rewrite (map_extend_app phi (ty_from_id_list (l1 ++ i::nil)) (ty_from_id_list P2)).
     rewrite (nth_error_app (map_extend_subst_type (ty_from_id_list (l1 ++ i::nil)) phi)
             (map_extend_subst_type (ty_from_id_list P2) phi)).
     erewrite (@nth_error_map phi (ty_from_id_list (l1 ++ i::nil)) (length l1) (var i)).
     erewrite (@inst_subst_to_subst_aux_4 G2 (var i) tau2 l2 L is_s phi); eauto.
     rewrite ty_from_id_list_app; simpl.
     rewrite <- length_ty_from_id_list; eauto.
     crush.
  - crush. 
  - 
    do 11 intro; intros more_gen_hyp disjoint1 disjoint2.
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

Hint Resolve more_general_gen_type_aux.

Lemma product_for_le_length : forall (l1 : list id) (l2 : list ty),
    length l1 <= length l2 -> exists s, product_list l1 l2 = Some s.
Proof.
  induction l1; crush.
  destruct l2; crush. 
  edestruct IHl1; eauto.
  apply le_S_n in H.
  apply H.
  rewrite H0.
  exists ((a, t)::x).
  reflexivity.
Qed.

Hint Resolve product_for_le_length.

Lemma length_Snd_gen_aux : forall (G : ctx) (tau : ty) (l : list id),
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
  rewrite length_app.
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

Lemma product_list_exists : forall (tau : ty) (G : ctx) (is_s : inst_subst),
    max_gen_vars (gen_ty tau G) <= length is_s ->
    exists s, product_list (snd (gen_ty_aux tau G nil)) is_s = Some s.
Proof.
  intros.
  apply product_for_le_length.
  rewrite length_Snd_gen_aux.
  crush.
Qed.


Lemma is_prefixe_reflexivity : forall C L : list id, is_prefixe_free2 C L L.
intros C L.
econstructor.
exists (nil: list id).
 split; auto.
 apply app_nil_end.
Qed.

Hint Resolve is_prefixe_reflexivity.

Lemma more_general_gen_ty : forall (G1 G2 : ctx) (t : ty),
    more_general_ctx G1 G2 -> more_general (gen_ty t G1) (gen_ty t G2).
Proof.
  intros.
  econstructor. intros.
  inverts* H0.
  unfold gen_ty in |- *; intros.
  destruct (product_list_exists t G2 x); eauto.
  unfold is_schm_instance.
  exists (map_extend_subst_type (ty_from_id_list (snd (gen_ty_aux t G1 nil))) x0).
  rewrite (@more_general_gen_type_aux G1 G2 t tau x0 nil nil
    (snd (gen_ty_aux t G2 nil)) (snd (gen_ty_aux t G1 nil)) x)
 ; eauto.
Qed.

Hint Resolve more_general_gen_ty.

Lemma has_type_var_ctx_diff : forall (i j : id) (G : ctx) (tau : ty) (sigma : schm),
    i <> j -> has_type G (var_t i) tau -> has_type ((j, sigma) :: G) (var_t i) tau.
Proof.
  intros.
  inversion_clear H0.
 econstructor; crush.
Qed.

Hint Resolve has_type_var_ctx_diff.

Lemma typing_in_a_more_general_ctx : forall (e : term) (G2 G1 : ctx) (t : ty),
    more_general_ctx G1 G2 -> has_type G2 e t -> has_type G1 e t.
Proof.
  induction e.
  - induction G2. intros.
    inverts* H0. crush.
    destruct a.
    intros.
    inversion_clear H.
    destruct (eq_id_dec i0 i).
    subst.
    inversion_clear H0.
    apply var_ht with (sigma:=sigma1); eauto.
    crush.
    simpl in H. destruct (eq_id_dec i i); intuition.
    inverts* H.
    inverts* H2.
    apply has_type_var_ctx_diff; eauto.
    eapply IHG2; eauto.
    inverts* H0.
    econstructor; crush.
  - intros.
    inverts* H0.
    econstructor; eauto.
  - intros.
    inverts* H0.
    econstructor.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
    auto.
  - intros.
    inverts* H0.
    econstructor; eauto.
    eapply IHe; eauto.
    econstructor; eauto.
  - intros.
    inverts* H.
    inverts* H0.
    econstructor.
Qed.
    
Hint Resolve typing_in_a_more_general_ctx.

Lemma more_general_ctx_refl : forall G : ctx, more_general_ctx G G.
simple induction G; auto.
intros; elim a; auto.
Qed.

Hint Resolve more_general_ctx_refl.

Lemma is_not_generalizable_aux : forall (G : ctx) (tau : ty) (l : list id),
    is_sublist_id (ids_ty tau) (FV_ctx G) ->
    gen_ty_aux tau G l = (ty_to_schm tau, l).
Proof.
  induction tau; crush.
Qed.

Hint Resolve is_not_generalizable_aux.

Lemma more_general_gen_ty_before_apply_subst_aux : forall (G : ctx) (tau1 tau2 : ty) (phi s : substitution)
                      (l1 l2 L P : list id) (is_s : inst_subst),
    are_disjoints (FV_ctx G) l1 ->
    are_disjoints (FV_ctx (apply_subst_ctx s G)) l2 ->
    apply_inst_subst is_s (fst (gen_ty_aux (apply_subst s tau1) (apply_subst_ctx s G) l2)) = Some tau2 ->
    is_prefixe_free2 (FV_ctx (apply_subst_ctx s G)) (snd (gen_ty_aux (apply_subst s tau1) (apply_subst_ctx s G) l2)) L ->
    product_list L is_s = Some phi ->
    is_prefixe_free2 (FV_ctx G) (snd (gen_ty_aux tau1 G l1)) P ->
    apply_inst_subst (map_extend_subst_type (ty_from_id_list P) (compose_subst s phi))
                     (apply_subst_schm s (fst (gen_ty_aux tau1 G l1))) = Some tau2.
Proof.
  induction tau1.
  - do 8 intro; simpl in |- *.
    intros disjoint1 disjoint2.
    repeat fold (apply_subst s (var i)) in *.
    cases (in_list_id i (FV_ctx G)).
    + simpl.
      repeat fold (apply_subst s (var i)) in *.
      erewrite is_not_generalizable_aux; eauto.
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
        erewrite inst_subst_to_subst_aux_4.
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
        erewrite inst_subst_to_subst_aux_4 with (l := l2); eauto.
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
    erewrite (@IHtau1_2 tau3 phi s) with (l2:= (snd (gen_ty_aux (apply_subst s tau1_1) (apply_subst_ctx s G) l2))); eauto.
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
  exists (map_extend_subst_type (ty_from_id_list (snd (gen_ty_aux tau G nil))) (compose_subst s x0)).
  eauto.
Qed.

Hint Resolve more_general_gen_ty_before_apply_subst.
