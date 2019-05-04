Set Implicit Arguments.

Require Import ListIds.
Require Import Subst.
Require Import SimpleTypes.
Require Import MyLtacs.
Require Import Disjoints.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import LibTactics.
Require Import Schemes.

Require Import LibTactics.


(** * Simple Substitution on schemes *)

Fixpoint apply_subst_schm (s : substitution) (sigma : schm) : schm :=
  match sigma with
  | sc_arrow l r => sc_arrow (apply_subst_schm s l) (apply_subst_schm s r)
  | sc_var i => ty_to_schm (apply_subst s (var i))
  | sc_con i => sc_con i
  | sc_gen i => sc_gen i
  end.

(** ** Some obvious facts about substitutions schemes **)

Lemma apply_subst_schm_id : forall t, apply_subst_schm nil t = t.
Proof.
  induction t ; mysimp.
  congruence.
Qed.

Hint Resolve apply_subst_schm_id.
Hint Rewrite apply_subst_schm_id:RE.

Lemma apply_subst_schm_con : forall s n, apply_subst_schm s (sc_con n) = sc_con n.
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_schm_con.
Hint Rewrite apply_subst_schm_con:RE.

Lemma apply_subst_schm_arrow : forall s l r, apply_subst_schm s (sc_arrow l r) = sc_arrow (apply_subst_schm s l) (apply_subst_schm s r).
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_schm_arrow.
Hint Rewrite apply_subst_schm_arrow:RE.

Lemma apply_subst_schm_gen : forall s n, apply_subst_schm s (sc_gen n) = sc_gen n.
Proof.
  induction s ; mysimp.
Qed.


Hint Resolve apply_subst_schm_gen.
Hint Rewrite apply_subst_schm_gen:RE.

Lemma apply_subst_schm_arrow_inversion1 : forall s sigma1 sigma2,
    apply_subst_schm s (sc_arrow sigma1 sigma2) = sc_arrow sigma1 sigma2 ->
    apply_subst_schm s sigma1 = sigma1.
Proof.
  intros.
  rewrite apply_subst_schm_arrow in H.
  inversion H.
  rewrite H1.
  rewrite H1.
  reflexivity.
Qed.

Hint Resolve apply_subst_schm_arrow_inversion1.
Hint Rewrite apply_subst_schm_arrow_inversion1:RE.

Lemma apply_subst_schm_arrow_inversion2 : forall s sigma1 sigma2,
    apply_subst_schm s (sc_arrow sigma1 sigma2) = sc_arrow sigma1 sigma2 ->
    apply_subst_schm s sigma2 = sigma2.
Proof.
  intros.
  rewrite apply_subst_schm_arrow in H.
  inversion H.
  rewrite H2.
  rewrite H2.
  reflexivity.
Qed.

Hint Resolve apply_subst_schm_arrow_inversion2.
Hint Rewrite apply_subst_schm_arrow_inversion2:RE.

Lemma apply_subst_schm_nil : forall sigma, apply_subst_schm nil sigma = sigma.
Proof.
  intros; induction sigma; mysimp.
  congruence.
Qed.

Hint Resolve apply_subst_schm_nil.
Hint Rewrite apply_subst_schm_nil : subst.

(** * Inst subst on schemes *)
(** * Substitution to make a scheme a simple type *)

Definition inst_subst := list ty.

Definition ids_inst_subst (s : inst_subst) : list id := List.concat (List.map ids_ty s).

Fixpoint apply_inst_subst (is: inst_subst) (sigma: schm) : schm_check:=
  match sigma with
  | (sc_con c) => (Some_schm (con c))
  | (sc_var v) => (Some_schm (var v))
  | (sc_gen x) => match (nth_error is x) with
                     | None => Error_schm
                     | (Some t) => (Some_schm t)
                 end
  | (sc_arrow ts1 ts2) => match (apply_inst_subst is ts1) with
                          | Error_schm => Error_schm
                          | (Some_schm t1) =>
                            match (apply_inst_subst is ts2) with
                             | Error_schm => Error_schm
                             | (Some_schm t2) => (Some_schm (arrow t1 t2))
                            end
                         end
end.

(** ** Some obvious facts about instance substitutions schemes **)

Lemma apply_inst_subst_con : forall (i : id) (is : inst_subst),
    apply_inst_subst is (sc_con i) = Some_schm (con i).
Proof.
  intros. reflexivity.
Qed.

Hint Resolve apply_inst_subst_con.
Hint Rewrite apply_inst_subst_con:RE.

Lemma apply_inst_subst_var : forall (i : id) (is : inst_subst),
    apply_inst_subst is (sc_var i) = Some_schm (var i).
Proof.
  intros. reflexivity.
Qed.

Hint Resolve apply_inst_subst_var.
Hint Rewrite apply_inst_subst_var:RE.

Lemma ty_to_subst_single : forall (tau t : ty) (i : id),
    apply_subst_schm ((i, t)::nil) (ty_to_schm tau) = ty_to_schm (apply_subst ((i, t)::nil) tau).
Proof.
  intros.
  induction tau; mysimp.
  rewrite IHtau1.
  rewrite IHtau2.
  reflexivity.
Qed.

Hint Resolve ty_to_subst_single.
Hint Rewrite ty_to_subst_single:RE.

Lemma ty_to_subst_schm : forall (s : substitution) (tau : ty),
    apply_subst_schm s (ty_to_schm tau) = ty_to_schm (apply_subst s tau).
Proof.
  intros.
  induction tau; eauto.
  - induction s.
      + rewrite apply_subst_nil. rewrite apply_subst_schm_nil. reflexivity.
      + crush.
Qed.

Hint Resolve ty_to_subst_schm.
Hint Rewrite ty_to_subst_schm:RE.


(** * Type instance definition **)

Definition is_schm_instance (tau : ty) (sigma : schm) :=
    exists is: inst_subst, (apply_inst_subst is sigma) = (Some_schm tau).


(**  Most general instance definition **)
Definition most_general_schm_instance (tau : ty) (sigma : schm) :=
  is_schm_instance tau sigma -> forall tau', is_schm_instance tau' sigma ->
                                    exists (s : substitution), tau' = apply_subst s tau.

(** ** Application of a simple substitution over a inst_subst *)
Definition map_apply_subst_ty (s : substitution) (is : inst_subst) : inst_subst :=
  List.map (apply_subst s) is.

(** Some facts about application of a simple substitution over a inst_subst  *)
Lemma apply_inst_subst_con_inversion : forall (is : inst_subst) (e : schm) (i : id),
    e = sc_con i -> apply_inst_subst is e = Some_schm (con i).
Proof.
  intros.
  subst.
  apply apply_inst_subst_con.
Qed.

Hint Resolve apply_inst_subst_con_inversion.
Hint Rewrite apply_inst_subst_con_inversion:RE.

Lemma apply_inst_ty_to_schm : forall (tau : ty) (is : inst_subst),
    apply_inst_subst is (ty_to_schm tau) = Some_schm tau.
Proof.
  intros.
  induction tau; mysimp.
  rewrite IHtau1.
  rewrite IHtau2.
  reflexivity.
Qed.

Hint Resolve apply_inst_ty_to_schm.
Hint Rewrite apply_inst_ty_to_schm:RE.

Lemma subst_inst_subst_type_var : forall (is : inst_subst) (s: substitution) (i : id),
    (apply_inst_subst is (sc_var i)) = (Some_schm (var i)) ->
    (apply_inst_subst (map_apply_subst_ty s is) (apply_subst_schm s (sc_var i))) =
    (Some_schm (apply_subst s (var i))).
Proof.
  induction is.
  simpl.
  - intros. induction s.
    + reflexivity.
    + mysimp.
  - intros. destruct s.
    + reflexivity.
    + erewrite <- apply_inst_ty_to_schm.
      fequals.
Qed.

Hint Resolve subst_inst_subst_type_var.
Hint Rewrite subst_inst_subst_type_var:RE.

Lemma apply_inst_subst_gen_nth : forall (is : inst_subst) (i : id) (tau : ty),
    apply_inst_subst is (sc_gen i) = Some_schm tau -> nth_error is i = Some tau.
Proof.
  intros.
  simpl in H.
  destruct (nth_error is i).
  inversion H. reflexivity.
  inversion H.
Qed.

Hint Resolve apply_inst_subst_gen_nth.
Hint Rewrite apply_inst_subst_gen_nth:RE.

Lemma nth_error_map_apply_subst : forall (is : inst_subst) (s : substitution) (i : id) (tau : ty),
    nth_error is i = Some tau ->
    nth_error (map_apply_subst_ty s is) i = Some (apply_subst s tau).
Proof.
  intros.
  apply map_nth_error.
  assumption.
Qed.

Hint Resolve nth_error_map_apply_subst.
Hint Rewrite nth_error_map_apply_subst:RE.

Lemma map_apply_subst_gen : forall (tau : ty) (s : substitution) (is : inst_subst) (i : id),
    apply_inst_subst is (sc_gen i) = Some_schm tau ->
    apply_inst_subst (map_apply_subst_ty s is) (sc_gen i) = Some_schm (apply_subst s tau).
Proof.
  induction tau;
    try (intros;
    apply apply_inst_subst_gen_nth in H as H';
    eapply nth_error_map_apply_subst in H';
    simpl;
    rewrite H';
    reflexivity).
Qed.

Hint Resolve map_apply_subst_gen.
Hint Rewrite map_apply_subst_gen:RE.

Lemma exist_arrow_apply_inst_arrow : forall (is : inst_subst) (sigma1 sigma2 : schm) (tau : ty),
    apply_inst_subst is (sc_arrow sigma1 sigma2) = Some_schm tau -> exists tau1 tau2, tau = arrow tau1 tau2.
Proof.
  intros.
  simpl in H.
    destruct (apply_inst_subst is sigma1).
    destruct (apply_inst_subst is sigma2).
    inversion H.
    exists t t0.
    reflexivity.
    inversion H.
    inversion H.
Qed.

Hint Resolve exist_arrow_apply_inst_arrow.
Hint Rewrite exist_arrow_apply_inst_arrow:RE.

Lemma and_arrow_apply_inst_arrow : forall (sigma1 sigma2 : schm) (tau tau' : ty) (is : inst_subst),
    apply_inst_subst is (sc_arrow sigma1 sigma2) = Some_schm (arrow tau tau') ->
    (apply_inst_subst is sigma1 = Some_schm tau) /\ (apply_inst_subst is sigma2 = Some_schm tau').
Proof.
  intros.
  split;
    try (simpl in H;
    destruct (apply_inst_subst is sigma1);
    destruct (apply_inst_subst is sigma2);
    inversion H; reflexivity;
    inversion H;
    inversion H).
Qed.

Hint Resolve and_arrow_apply_inst_arrow.
Hint Rewrite and_arrow_apply_inst_arrow:RE.

Lemma exist_arrow_apply_inst_arrow2 : forall (sigma1 sigma2 : schm) (tau : ty) (is : inst_subst),
    apply_inst_subst is (sc_arrow sigma1 sigma2) = Some_schm tau ->
    exists tau1 tau2, (apply_inst_subst is sigma1 = Some_schm tau1) /\ (apply_inst_subst is sigma2 = Some_schm tau2) /\
                 arrow tau1 tau2 = tau.
Proof.
  intros.
  simpl in H.
    destruct (apply_inst_subst is sigma1); crush.
    destruct (apply_inst_subst is sigma2); crush.
    inversion H.
    inversion H.
Qed.

Hint Resolve exist_arrow_apply_inst_arrow2.

Lemma subst_inst_subst_type:
  forall (sigma : schm) (s: substitution) (is : inst_subst) (tau : ty),
    (apply_inst_subst is sigma) = (Some_schm tau) ->
    (apply_inst_subst (map_apply_subst_ty s is) (apply_subst_schm s sigma)) =
    (Some_schm (apply_subst s tau)).
Proof.
  induction sigma.
  - intros.
    rewrite apply_inst_subst_var in H.
    inversion H.
    induction s.
    + reflexivity. 
    + apply subst_inst_subst_type_var.
      reflexivity.
  - intros.
    rewrite apply_inst_subst_con in H. 
    inversion H.
    rewrite apply_subst_con. 
    apply apply_inst_subst_con_inversion.
    apply apply_subst_schm_con.
  - intros.
    rewrite apply_subst_schm_gen.
    apply map_apply_subst_gen.
    assumption.
  - intros.
    eapply exist_arrow_apply_inst_arrow in H as H'.
    destruct H'.
    destruct H0.
    rewrite H0 in *.
    specialize IHsigma1 with (s:=s) (is:=is) (tau:=x).
    specialize IHsigma2 with (s:=s) (is:=is) (tau:=x0).
    rewrite apply_subst_schm_arrow.
    simpl in *.
    rewrite IHsigma1.
    rewrite IHsigma2.
    reflexivity.
    apply and_arrow_apply_inst_arrow in H.
    destruct H.
    auto.
    apply and_arrow_apply_inst_arrow in H.
    destruct H.
    auto.
Qed.

Hint Resolve subst_inst_subst_type.
Hint Rewrite subst_inst_subst_type:RE.

(* Lemmas about FV_schm *)
Lemma FV_type_scheme_type_to_type_scheme : forall (tau : ty),
    (FV_schm (ty_to_schm tau)) = (ids_ty tau).
Proof.
  intros.
  induction tau; try reflexivity.
  simpl. rewrite IHtau1. rewrite IHtau2. reflexivity.
Qed.

Hint Resolve FV_type_scheme_type_to_type_scheme.
Hint Rewrite FV_type_scheme_type_to_type_scheme:RE.

Lemma not_in_FV_type_scheme : forall  (s: substitution) (sigma : schm) (st: id) ,
    in_list_id st (img_ids s) = false -> in_list_id st (FV_schm sigma) = false ->
    in_list_id st (FV_schm (apply_subst_schm s sigma)) = false.
Proof.
  intros.
   induction sigma.
  - induction s.
    + rewrite apply_subst_schm_nil. assumption.
    + destruct a.
      simpl.
      destruct (eq_id_dec i0 i).
      unfold img_ids in H.
      simpl in H.
      apply in_list_id_append_inversion1 in H.
      fold (img_ids s) in H.
      induction t; simpl in *; mysimp; eauto.
      eapply in_list_id_and_append; splits; eauto.
      fold (apply_subst_schm s (sc_var i)).
      unfold img_ids in H.
      simpl in H.
      apply in_list_id_append_inversion2 in H.
      eauto.
  - reflexivity.
  - reflexivity.
  - simpl in *.
    apply in_list_id_append_inversion1 in H0 as H0'.
    apply in_list_id_append_inversion2 in H0 as H0''.
    eauto.
Qed.      

Hint Resolve not_in_FV_type_scheme.
Hint Rewrite not_in_FV_type_scheme:RE.

(** Identity condition for apply_subst_schm *)
Lemma subst_schm_when_dom_s_disjoint_with_FV_schm : forall (s: substitution) (sigma: schm),
    (are_disjoints (dom s) (FV_schm sigma)) -> (apply_subst_schm s sigma) = sigma.
Proof.
  induction s; intros; eauto.
  destruct a.
  induction sigma; simpl in *; mysimp.
  unfold are_disjoints in H.
  specialize H with (x:=i0).
  simpl in H. destruct (eq_id_dec i0 i0); intuition.
  specialize IHs with (sigma:= sc_var i0).
  simpl in IHs.
  apply IHs. 
  eapply are_disjoints_cons_l; eauto.
  apply disjoint_list_and_append_inversion1 in H as H'.
  apply disjoint_list_and_append_inversion2 in H as H''.
  fequals; eauto.
Qed.  

Hint Resolve subst_schm_when_dom_s_disjoint_with_FV_schm.
Hint Rewrite subst_schm_when_dom_s_disjoint_with_FV_schm:RE.

Lemma apply_schm_compose_equiv : forall s1 s2 sigma, apply_subst_schm (compose_subst s1 s2) sigma =
                                                apply_subst_schm s2 (apply_subst_schm s1 sigma).
Proof.
  intros.
  induction s1; intros; mysimp. rewrite apply_subst_schm_nil. rewrite compose_subst_nil_l.  reflexivity.
  induction sigma; mysimp; simpl in *; eauto.
  inversion IHs1.
  fequals; eauto.
Qed.

Hint Resolve apply_schm_compose_equiv.
Hint Rewrite apply_schm_compose_equiv:RE.

Fixpoint compute_inst_subst (st : id) (n : nat) : list ty :=
  match n with
  | 0 => nil
  | S n' =>
    match compute_inst_subst (S st) n' with
    | l' => (var st :: l')
    end
  end.

Lemma nth_error_nil : forall i, nth_error (nil : list ty) i = None.
Proof.
  intros.
  induction i; mysimp.
Qed.

Hint Resolve nth_error_nil.
Hint Rewrite nth_error_nil:RE.

Lemma nth_error_compute_inst_Some : forall i k j, i < k -> nth_error (compute_inst_subst j k) i = Some (var (i + j)).
Proof.
  induction i.
  - intros. destruct k.
    + inversion H.
    + reflexivity.
  - intros. destruct k.
    + inversion H.
    + simpl.
      erewrite IHi.
      fequals.
      fequals.
      omega.
      omega.
Qed.

Hint Resolve nth_error_compute_inst_Some.
Hint Rewrite nth_error_compute_inst_Some:RE.

Lemma nth_error_compute_inst_None' : forall i j, nth_error (compute_inst_subst j i) i = None.
Proof.
  induction i.
  - intros. reflexivity.
  - intros. simpl. auto.
Qed.

Hint Resolve nth_error_compute_inst_None'.
Hint Rewrite nth_error_compute_inst_None':RE.

Lemma nth_error_None_None_cons : forall i (l : list ty) a, nth_error (a :: l) i = None -> nth_error l i = None.
Proof.
  induction i; intros. simpl in *. inversion H.
  simpl in *.
  induction l. reflexivity.
  eapply IHi.
  apply H.
Qed.

Hint Resolve nth_error_None_None_cons.
Hint Rewrite nth_error_None_None_cons:RE.

Lemma nth_error_None_None : forall (l : list ty) i, nth_error l i = None -> nth_error l (S i) = None.
Proof.
  intros.
  induction l.
  erewrite nth_error_nil.
  reflexivity.
  apply nth_error_None_None_cons in H.
  auto.
Qed.

Hint Resolve nth_error_None_None.
Hint Rewrite nth_error_None_None:RE.

Lemma nth_error_None_None_S : forall k i j, nth_error (compute_inst_subst j k) i = None -> nth_error (compute_inst_subst (S j) k) i = None.
Proof.
  induction k; intros. simpl. auto.
  induction i. simpl in *. inversion H.
  simpl. auto.
Qed.

Hint Resolve nth_error_None_None_S.
Hint Rewrite nth_error_None_None_S:RE.

Lemma nth_error_compute_inst_None : forall i k j, k < i -> nth_error (compute_inst_subst j k) i = None.
Proof.
  induction i.
  - intros. inversion H.
  - intros.
    induction k.
    simpl in *. reflexivity.
    specialize IHi with (j := j) (k := k).
    apply nth_error_None_None_S.
    apply IHi.
    omega.
Qed.

Hint Resolve nth_error_compute_inst_None.
Hint Rewrite nth_error_compute_inst_None:RE.

(** * About computing the subst s' in the completeness proof **)

Fixpoint compute_subst (i : id) (l : list ty) : substitution :=
  match l return substitution with
  | nil => nil
  | t :: l' => (i, t) :: compute_subst (S i) l'
  end.

Lemma not_in_domain_compute : forall (is_s : inst_subst) (st0 st1 : id),
    st0 < st1 -> find_subst (compute_subst st1 is_s) st0 = None.
Proof.
  induction is_s; crush.
Qed.

Hint Resolve not_in_domain_compute.
Hint Rewrite not_in_domain_compute:RE.

Lemma find_subst_some_apply_app_compute_subst : forall (is_s : inst_subst) (s : substitution) (st0 st1 : id),
       st0 < st1 -> apply_subst ((compute_subst st1 is_s) ++ s) (var st0) = apply_subst s (var st0).
Proof.
  induction is_s;
  crush.
Qed.

Hint Resolve find_subst_some_apply_app_compute_subst.
Hint Rewrite find_subst_some_apply_app_compute_subst:RE.

Lemma compute_subst_cons_rwt : forall (st : id) (tau : ty) (is_s : inst_subst),
    compute_subst st (tau :: is_s) = (st, tau) :: compute_subst (S st) is_s.
Proof.
  auto.
Qed.

Hint Resolve compute_subst_cons_rwt.
Hint Rewrite compute_subst_cons_rwt:RE.

Lemma find_subst_id_compute : forall (i : id) (is_s : inst_subst) (st : id) (tau : ty),
    nth_error is_s i = Some tau -> find_subst (compute_subst st is_s) ((st + i)) = Some tau.
Proof.
  induction i; crush.
  destruct is_s; crush.
  destruct is_s. crush.
  rewrite compute_subst_cons_rwt.
  crush.
  rewrite <- Nat.add_succ_comm.
  erewrite IHi; eauto.
Qed.

Hint Resolve find_subst_id_compute.
Hint Rewrite find_subst_id_compute:RE.

Lemma apply_subst_inst_to_ty_to_schm : forall (is_s : inst_subst) (tau : ty),
    apply_inst_subst is_s (ty_to_schm tau) = Some_schm tau.
Proof.
  induction tau; crush.
Qed.

Hint Resolve apply_subst_inst_to_ty_to_schm.
Hint Rewrite apply_subst_inst_to_ty_to_schm:RE.

