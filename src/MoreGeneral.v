Set Implicit Arguments.

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
Admitted.

Hint Resolve ty_from_id_list_app.
Hint Rewrite ty_from_id_list_app:RE.

Fixpoint map_extend_subst_type (l : list ty) (s2 : substitution) :=
  match l with
  | nil => nil
  | t::l' => apply_subst s2 t :: map_extend_subst_type l' s2
  end.

Lemma map_extend_app : forall (s : substitution) (l1 l2 : list ty),
    map_extend_subst_type (l1 ++ l2) s = map_extend_subst_type l1 s ++ map_extend_subst_type l2 s.
Admitted.

Hint Resolve map_extend_app.
Hint Rewrite map_extend_app:RE.

Inductive is_prefixe_free2 : list id -> list id -> list id -> Prop :=
  prefixe_free2_intro : forall C l L : list id,
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

Fixpoint find_generic_instance (sigma : schm) (tau : ty) :=
  match sigma with
  | sc_con i => con i
  | sc_var i => var i
  | sc_gen st => tau
  | sc_arrow sigma1 sigma2 => arrow (find_generic_instance sigma1 tau) (find_generic_instance sigma2 tau)
  end.

Fixpoint make_constant_gen_subst (n : id) (tau : ty)  :=
  match n with
  | O => nil 
  | S p => tau :: make_constant_gen_subst p tau
  end.
Lemma nth_make_constant_gen_subst3 : forall (p n : id) (tau : ty),
    S n <= p -> nth_error (make_constant_gen_subst p tau) n = Some tau.
Proof.
  induction p; crush.
  destruct n; crush.
  apply IHp.
  auto with *.
Qed.

Hint Resolve nth_make_constant_gen_subst3.
Hint Rewrite nth_make_constant_gen_subst3:RE.

Lemma apply_subst_inst_make_constant_gen_subst : forall (sigma : schm) (tau : ty) (p : id),
    max_gen_vars sigma <= p ->
    apply_inst_subst (make_constant_gen_subst p tau) sigma = Some_schm (find_generic_instance sigma tau).
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
  info_eauto with *.
  simpl in le.
  pose proof (PeanoNat.Nat.le_max_l (max_gen_vars sigma1) (max_gen_vars sigma2)).
  auto with *.
Qed.

Hint Resolve apply_subst_inst_make_constant_gen_subst.
Hint Resolve apply_subst_inst_make_constant_gen_subst:RE.

Lemma find_generic_instance_gen_instance_ts : forall (sigma : schm) (tau : ty),
    is_schm_instance (find_generic_instance sigma tau) sigma.
Proof.
  intros.
  unfold is_schm_instance.
  exists (make_constant_gen_subst (max_gen_vars sigma) tau).
  auto.
Qed.

Hint Resolve find_generic_instance_gen_instance_ts.
Hint Rewrite find_generic_instance_gen_instance_ts:RE.

Lemma sc_var_more_general_than_sigma : forall (sigma : schm) (st : id),
    more_general (sc_var st) sigma -> sigma = sc_var st.
Proof.
  intros.
  inversion H. subst.
  cut (is_schm_instance (find_generic_instance sigma (con 0)) sigma); eauto.
  intros.
  cut (is_schm_instance (find_generic_instance sigma (con 0)) (sc_var st)); eauto.
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

Lemma arrow_sigma_more_general_than_arrow : forall sigma sigma1 sigma2 : schm,
    (forall tau : ty, is_schm_instance tau sigma -> is_schm_instance tau (sc_arrow sigma1 sigma2)) ->
    {sig_sig : schm * schm | sigma = sc_arrow (fst sig_sig) (snd sig_sig)}.
Proof.
  Admitted.

Hint Resolve arrow_sigma_more_general_than_arrow.
Hint Resolve arrow_sigma_more_general_than_arrow:RE.

Lemma more_general_arrow_inversion1 : forall sigma1 sigma2 sigma1' sigma2' : schm,
    more_general (sc_arrow sigma1 sigma2) (sc_arrow sigma1' sigma2') ->
    more_general sigma1 sigma1'.
Admitted.

Hint Resolve more_general_arrow_inversion1.

Lemma more_general_arrow_inversion2 : forall sigma1 sigma2 sigma1' sigma2' : schm,
    more_general (sc_arrow sigma1 sigma2) (sc_arrow sigma1' sigma2') ->
    more_general sigma2 sigma2'.
Admitted.

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

Lemma nth_app : forall (l l1 : list ty) (n : id), n < length l -> nth_error (l ++ l1) n = nth_error l n.
Admitted.

Hint Resolve nth_app.
Hint Rewrite nth_app:RE.

Lemma inst_subst_to_subst_aux_4 : forall (G : ctx) (tau1 tau2 : ty) (l L : list id)
                                   (is_s : list ty) (phi : substitution),
    are_disjoints (FV_ctx G) l ->
    apply_inst_subst is_s (fst (gen_ty_aux tau1 G l)) = Some_schm tau2 ->
    is_prefixe_free2 (FV_ctx G) (snd (gen_ty_aux tau1 G l)) L ->
    product_list L is_s = Some phi -> apply_subst phi tau1 = tau2.
Admitted.

Hint Resolve inst_subst_to_subst_aux_4.
Hint Rewrite inst_subst_to_subst_aux_4:RE.

Lemma nth_map : forall (s : substitution) (x : list ty) (n : id) (tau : ty),
    nth_error x n = Some tau ->
    nth_error (map_extend_subst_type x s) n = Some (apply_subst s tau).
Admitted.

Hint Resolve nth_map.
Hint Rewrite nth_map:RE.

Lemma index_list_id_nth : forall (l : list id) (v : id) (k : id),
    index_list_id v l = Some k -> nth_error (ty_from_id_list l) k = Some (var v).
Admitted.

Hint Resolve index_list_id_nth.
Hint Rewrite index_list_id_nth:RE.

Lemma length_map : forall (s : substitution) (l : list ty),
    length (map_extend_subst_type l s) = length l.
Admitted.

Hint Resolve length_map.
Hint Rewrite length_map:RE.

Lemma length_ty_from_id_list : forall l : list id, length (ty_from_id_list l) = length l.
Admitted.

Hint Resolve length_ty_from_id_list.
Hint Rewrite length_ty_from_id_list:RE.

Lemma index_lt : forall (l : list id) (st : id) (k : id),
    index_list_id st l = Some k -> k < length l.
Admitted.

Hint Resolve index_lt.

Lemma nth_app_cons : forall (l : list ty) (tau : ty), nth_error (l ++ tau::nil) (length l) = Some tau.
simple induction l; auto.
Qed.

Hint Resolve nth_app_cons.

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

Lemma Snd_gen_aux_with_app3 : forall (G : ctx) (tau : ty) (l : list id),
    exists l', snd (gen_ty_aux tau G l) = l ++ l' /\ are_disjoints (FV_ctx G) l'.
Admitted.

Hint Resolve Snd_gen_aux_with_app3.

Lemma disjoint_Snd_gen_aux : forall (G : ctx) (l : list id) (tau : ty),
    are_disjoints (FV_ctx G) l -> are_disjoints (FV_ctx G) (snd (gen_ty_aux tau G l)).
intros.
elim (Snd_gen_aux_with_app3 G tau l).
intros l' Hyp; elim Hyp; clear Hyp; intros; rewrite H0.
eauto.
Qed.

Hint Resolve disjoint_Snd_gen_aux.

Lemma is_prefixe2_gen_aux : forall (l L : list id) (tau : ty) (G : ctx),
    is_prefixe_free2 (FV_ctx G) (snd (gen_ty_aux tau G l)) L ->
    is_prefixe_free2 (FV_ctx G) l L.
Admitted.

Hint Resolve is_prefixe2_gen_aux.

Lemma more_general_gen_type_aux : forall (G1 G2 : ctx) (tau1 tau2 : ty) (phi : substitution)
                                    (l2 l1 L P : list id) (is_s : inst_subst),
    more_general_ctx G1 G2 -> are_disjoints (FV_ctx G2) l2 ->
    are_disjoints (FV_ctx G1) l1 ->
    apply_inst_subst is_s (fst (gen_ty_aux tau1 G2 l2)) = Some_schm tau2 ->
    is_prefixe_free2 (FV_ctx G2) (snd (gen_ty_aux tau1 G2 l2)) L ->
    product_list L is_s = Some phi ->
    is_prefixe_free2 (FV_ctx G1) (snd (gen_ty_aux tau1 G1 l1)) P ->
    apply_inst_subst (map_extend_subst_type (ty_from_id_list P) phi)
                     (fst (gen_ty_aux tau1 G1 l1)) = Some_schm tau2.
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
     rewrite (nth_app (map_extend_subst_type (ty_from_id_list l1) phi) (map_extend_subst_type (ty_from_id_list x) phi)).
     erewrite (@nth_map phi (ty_from_id_list l1) i0 (var i)).
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
     rewrite (nth_app (map_extend_subst_type (ty_from_id_list (l1 ++ i::nil)) phi)
             (map_extend_subst_type (ty_from_id_list P2) phi)).
     erewrite (@nth_map phi (ty_from_id_list (l1 ++ i::nil)) (length l1) (var i)).
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

Lemma product_list_exists : forall (tau : ty) (G : ctx) (is_s : inst_subst),
    max_gen_vars (gen_ty tau G) <= length is_s ->
    {s : substitution | product_list (snd (gen_ty_aux tau G nil)) is_s = Some s}.
Proof.
unfold gen_ty in |- *; intros.
Admitted.

Lemma is_instance_le_max : forall (sigma : schm) (tau : ty) (is_s : inst_subst),
    apply_inst_subst is_s sigma = Some_schm tau -> max_gen_vars sigma <= length is_s.
Admitted.

Hint Resolve is_instance_le_max.

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
  - skip.
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
Admitted.

Hint Resolve is_not_generalizable_aux.

Lemma s_gen_aux_7 : forall (G : ctx) (tau1 tau2 : ty) (phi s : substitution)
                      (l1 l2 L P : list id) (is_s : inst_subst),
    are_disjoints (FV_ctx G) l1 ->
    are_disjoints (FV_ctx (apply_subst_ctx s G)) l2 ->
    apply_inst_subst is_s (fst (gen_ty_aux (apply_subst s tau1) (apply_subst_ctx s G) l2)) = Some_schm tau2 ->
    is_prefixe_free2 (FV_ctx (apply_subst_ctx s G)) (snd (gen_ty_aux (apply_subst s tau1) (apply_subst_ctx s G) l2)) L ->
    product_list L is_s = Some phi ->
    is_prefixe_free2 (FV_ctx G) (snd (gen_ty_aux tau1 G l1)) P ->
    apply_inst_subst (map_extend_subst_type (ty_from_id_list P) (compose_subst s phi))
                     (apply_subst_schm s (fst (gen_ty_aux tau1 G l1))) = Some_schm tau2.
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
        rewrite nth_app; eauto.
        erewrite nth_map; eauto.
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
        rewrite nth_app; eauto.
        erewrite nth_map; eauto.
        rewrite apply_compose_equiv.
        erewrite inst_subst_to_subst_aux_4 with (l := l2); eauto.
        rewrite ty_from_id_list_app.
        simpl.
        erewrite <- length_ty_from_id_list; eauto.
        rewrite length_map2.
        rewrite length_app_cons. eauto.
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

Hint Resolve s_gen_aux_7.

Lemma s_gen_t_more_general_than_gen_s_t : forall (s : substitution) (G : ctx) (tau : ty),
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
  crush.
Qed.

Hint Resolve s_gen_t_more_general_than_gen_s_t.
