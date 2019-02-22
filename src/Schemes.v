Set Implicit Arguments.

Require Import ListIds.
Require Import Unify.
Require Import Disjoints.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.

Require Import LibTactics.

(** * Schemes *)
      
Inductive schm : Type :=
  | sc_var : id -> schm
  | sc_con : id -> schm
  | sc_gen : id -> schm
  | sc_arrow : schm -> schm -> schm. 

(** * Substitutions for Schemes *)

Fixpoint ty_to_schm (tau : ty) : schm :=
match tau with
  | var n => sc_var n
  | con n => sc_con n
  | arrow t1 t2 => sc_arrow (ty_to_schm t1) (ty_to_schm t2)                 
end.

Fixpoint sub_schm (tau : ty) (x : id) (sigma : schm) : schm :=
match sigma with
    | sc_var n => if eq_id_dec x n then (ty_to_schm tau) else sc_var n
    | sc_con n => sc_con n
    | sc_gen n => sc_gen n
    | sc_arrow l r => sc_arrow (sub_schm tau x l) (sub_schm tau x r)
end.

Fixpoint apply_subst_schm (s : substitution) (t : schm) : schm :=
  match s with
    | nil => t
    | (v,t') :: s' => apply_subst_schm s' (sub_schm t' v t)
  end.

Lemma apply_subst_schm_end : forall s i t t',
    apply_subst_schm (s ++ (i,t) :: nil) t' = sub_schm t i (apply_subst_schm s t').
Proof.
  induction s ; mysimp.
Qed.

Lemma apply_subst_schm_append : forall s2 s1 t,
    apply_subst_schm (s1 ++ s2) t = apply_subst_schm s2 (apply_subst_schm s1 t).
Proof.
  induction s2 ; intros ; simpl. rewrite <- app_nil_end ; auto.
  assert (s1 ++ a :: s2 = (s1 ++ (a::nil)) ++ s2).
  rewrite app_ass ; auto. rewrite H. destruct a. rewrite (IHs2 (s1 ++ (i,t0)::nil)).
  rewrite <- apply_subst_schm_end. auto.
Qed.

Lemma apply_subst_schm_con : forall s n, apply_subst_schm s (sc_con n) = sc_con n.
Proof.
  induction s ; mysimp.
Qed.

Lemma apply_subst_schm_gen : forall s n, apply_subst_schm s (sc_gen n) = sc_gen n.
Proof.
  induction s ; mysimp.
Qed.

Lemma apply_subst_schm_arrow : forall s t1 t2,
                    apply_subst_schm s (sc_arrow t1 t2) =
                    sc_arrow (apply_subst_schm s t1) (apply_subst_schm s t2).
Proof.
  induction s ; mysimp.
Qed.


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

(** * Substitution to make a Scheme a simple Type *)

Definition inst_subst := list ty.

Definition ids_inst_subst (s : inst_subst) : list id := List.concat (List.map ids_ty s).

Inductive schm_check : Type :=
  | Some_schm : ty -> schm_check
  | Error_schm : schm_check.

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

Lemma apply_inst_subst_con : forall (i : id) (is : inst_subst),
    apply_inst_subst is (sc_con i) = Some_schm (con i).
Proof.
  intros. reflexivity.
Qed.

Lemma apply_inst_subst_var : forall (i : id) (is : inst_subst),
    apply_inst_subst is (sc_var i) = Some_schm (var i).
Proof.
  intros. reflexivity.
Qed.

Lemma ty_to_sub : forall (tau t : ty) (i : id),
    sub_schm t i (ty_to_schm tau) = ty_to_schm (sub t i tau).
Proof.
  intros.
  induction tau; mysimp.
  rewrite IHtau1.
  rewrite IHtau2.
  reflexivity.
Qed.

Lemma ty_to_subst_schm : forall (s : substitution) (tau : ty),
    apply_subst_schm s (ty_to_schm tau) = ty_to_schm (apply_subst s tau).
Proof.
  induction s.
  - intros. reflexivity.
  - intros. simpl.
    destruct a.
    destruct tau.
    + simpl.
      destruct (eq_id_dec i i0); intuition.
      rewrite <- IHs.
      simpl.
      reflexivity.
    + simpl. rewrite <- IHs. reflexivity.
    + rewrite <- IHs. simpl.
      fequals.
      fequals.
      apply ty_to_sub.
      apply ty_to_sub.
Qed.

Definition is_schm_instance (tau : ty) (sigma : schm) :=
    exists is: inst_subst, (apply_inst_subst is sigma) = (Some_schm tau).

Definition most_general_schm_instance (tau : ty) (sigma : schm) :=
  is_schm_instance tau sigma -> forall tau', is_schm_instance tau' sigma ->
                                    exists (s : substitution), tau' = apply_subst s tau.

Definition map_apply_subst_ty (s : substitution) (is : inst_subst) : inst_subst :=
  List.map (apply_subst s) is.

Lemma apply_inst_subst_con_inversion : forall (is : inst_subst) (e : schm) (i : id),
    e = sc_con i -> apply_inst_subst is e = Some_schm (con i).
Proof.
  intros.
  subst.
  apply apply_inst_subst_con.
Qed.

Lemma apply_inst_ty_to_schm : forall (tau : ty) (is : inst_subst),
    apply_inst_subst is (ty_to_schm tau) = Some_schm tau.
Proof.
  intros.
  induction tau; mysimp.
  rewrite IHtau1.
  rewrite IHtau2.
  reflexivity.
Qed.

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
      rewrite ty_to_subst_schm.
      rewrite apply_inst_ty_to_schm.
      reflexivity.
  - intros. destruct s.
    + reflexivity.
    + erewrite <- apply_inst_ty_to_schm.
      fequals.
      cut (sc_var i = ty_to_schm (var i)).
      intros.
      rewrite H0.
      rewrite ty_to_subst_schm.
      reflexivity.
      reflexivity.
Qed.

Lemma apply_inst_subst_gen_nth : forall (is : inst_subst) (i : id) (tau : ty),
    apply_inst_subst is (sc_gen i) = Some_schm tau -> nth_error is i = Some tau.
Proof.
  intros.
  simpl in H.
  destruct (nth_error is i).
  inversion H. reflexivity.
  inversion H.
Qed.

Lemma nth_error_map_apply_subst : forall (is : inst_subst) (s : substitution) (i : id) (tau : ty),
    nth_error is i = Some tau ->
    nth_error (map_apply_subst_ty s is) i = Some (apply_subst s tau).
Proof.
  intros.
  apply map_nth_error.
  assumption.
Qed.

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
    rewrite apply_subst_arrow.
    reflexivity.
    apply and_arrow_apply_inst_arrow in H.
    destruct H.
    auto.
    apply and_arrow_apply_inst_arrow in H.
    destruct H.
    auto.
Qed.

(** * Free variables of schemes *)

Fixpoint FV_schm (sigma : schm) : list id :=
  match sigma with
  | sc_var i => i::nil
  | sc_arrow l r => (FV_schm l) ++ (FV_schm r)
  | _ => nil
  end.

Lemma FV_type_scheme_type_to_type_scheme : forall (tau : ty),
    (FV_schm (ty_to_schm tau)) = (ids_ty tau).
Proof.
  intros.
  induction tau; try reflexivity.
  simpl. rewrite IHtau1. rewrite IHtau2. reflexivity.
Qed.

Lemma not_in_FV_type_scheme : forall  (sigma : schm) (st: id) (s: substitution),
    (in_list_id st (img_ids s)) = false ->
    (in_list_id st (FV_schm sigma))=false ->
    (in_list_id st (FV_schm (apply_subst_schm s sigma)))=false.
Proof.
  induction sigma; intros.
  - simpl in *.
    destruct (eq_id_dec i st); intuition.
    assert (sc_var i = ty_to_schm (var i)). {reflexivity. }
                                            rewrite H1.                                           
    rewrite ty_to_subst_schm.
    rewrite FV_type_scheme_type_to_type_scheme.
    eapply not_in_img; auto.
  - rewrite apply_subst_schm_con. reflexivity.
  - rewrite apply_subst_schm_gen. reflexivity.
  - rewrite apply_subst_schm_arrow. simpl.
    eapply in_list_id_and_append.
    simpl in H0. apply in_list_id_and_append_inversion in H0.
    destruct H0.
    split; auto.
Qed.

(** Identity condition for apply_subst_schm *)
Lemma subst_schm_when_dom_s_disjoint_with_FV_schm : forall (s: substitution) (sigma: schm),
    (are_disjoints (dom s) (FV_schm sigma)) -> (apply_subst_schm s sigma) = sigma.
Proof.
  intros.
  induction s.
  - simpl in H.
    reflexivity.
  - induction sigma, a.
    + simpl in H.
      apply are_disjoints_cons_diff in H as diff.
      simpl.
      destruct (eq_id_dec i0 i); try contradiction.
      apply are_disjoints_cons_l in H.
      auto.
    +
      simpl in *.
      apply are_disjoints_cons_l in H.
      auto.
    + simpl in *.
      apply are_disjoints_cons_l in H.
      auto.
    +
      simpl in H, IHs.
      rewrite apply_subst_schm_arrow.
      rewrite <- IHsigma1 at 2.
      rewrite <- IHsigma2 at 2.
      reflexivity.
      simpl.
      apply disjoint_list_and_append_inversion2 in H.
      assumption.
      intros.
      apply are_disjoints_cons_l in H.
      apply IHs in H.
      apply apply_subst_schm_arrow_inversion2 in H.
      assumption.
      simpl.
      apply disjoint_list_and_append_inversion1 in H.
      assumption.
      intros.
      apply are_disjoints_cons_l in H.
      apply IHs in H.
      apply apply_subst_schm_arrow_inversion1 in H.
      assumption.
Qed.      
