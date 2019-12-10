(** * The substitution over schemes
      This file contains the defintions of the two substitutions of schemes:
      [apply_subst_schm] and [apply_inst_subst].
      And several lemmas about both.
    *)

Set Implicit Arguments.

Require Import SimpleTypes.
Require Import SimpleTypesNotations.
Require Import ListIds.
Require Import Subst.
Require Import MyLtacs.
Require Import Disjoints.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import LibTactics.
Require Import Schemes.
Require Import NthErrorTools.

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

Hint Resolve apply_subst_schm_id:core.
Hint Rewrite apply_subst_schm_id:RE.

Lemma apply_subst_schm_con : forall s n, apply_subst_schm s (sc_con n) = sc_con n.
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_schm_con:core.
Hint Rewrite apply_subst_schm_con:RE.

Lemma apply_subst_schm_arrow : forall s l r, apply_subst_schm s (sc_arrow l r) = sc_arrow (apply_subst_schm s l) (apply_subst_schm s r).
Proof.
  induction s ; mysimp.
Qed.

Hint Resolve apply_subst_schm_arrow:core.
Hint Rewrite apply_subst_schm_arrow:RE.

Lemma apply_subst_schm_gen : forall s n, apply_subst_schm s (sc_gen n) = sc_gen n.
Proof.
  induction s ; mysimp.
Qed.


Hint Resolve apply_subst_schm_gen:core.
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

Hint Resolve apply_subst_schm_arrow_inversion1:core.
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

Hint Resolve apply_subst_schm_arrow_inversion2:core.
Hint Rewrite apply_subst_schm_arrow_inversion2:RE.

Lemma apply_subst_schm_nil : forall sigma, apply_subst_schm nil sigma = sigma.
Proof.
  intros; induction sigma; mysimp.
  congruence.
Qed.

Hint Resolve apply_subst_schm_nil:core.
Hint Rewrite apply_subst_schm_nil : subst.

(** * Instance subst on schemes *)
(** * Substitution to make a scheme a simple type *)

Definition inst_subst := list ty.

Definition ids_inst_subst (s : inst_subst) : list id := List.concat (List.map ids_ty s).

Fixpoint apply_inst_subst (is_s : inst_subst) (sigma: schm) : option ty:=
  match sigma with
  | (sc_con c) => (Some (con c))
  | (sc_var v) => (Some (var v))
  | (sc_gen x) => match (nth_error is_s x) with
                     | None => None
                     | (Some t) => (Some t)
                 end
  | (sc_arrow ts1 ts2) => match (apply_inst_subst is_s ts1) with
                          | None => None
                          | (Some t1) =>
                            match (apply_inst_subst is_s ts2) with
                             | None => None
                             | (Some t2) => (Some (arrow t1 t2))
                            end
                         end
end.

(** ** Some obvious facts about instance substitutions schemes **)

Lemma apply_inst_subst_con : forall (i : id) (is_s : inst_subst),
    apply_inst_subst is_s (sc_con i) = Some (con i).
Proof.
  intros. reflexivity.
Qed.

Hint Resolve apply_inst_subst_con:core.
Hint Rewrite apply_inst_subst_con:RE.

Lemma apply_inst_subst_var : forall (i : id) (is_s : inst_subst),
    apply_inst_subst is_s (sc_var i) = Some (var i).
Proof.
  intros. reflexivity.
Qed.

Hint Resolve apply_inst_subst_var:core.
Hint Rewrite apply_inst_subst_var:RE.

(** * Lemmas relation scheme substitution and ty_to_schm *)

Lemma ty_to_subst_single : forall (tau t : ty) (i : id),
    apply_subst_schm ((i, t)::nil) (ty_to_schm tau) = ty_to_schm (apply_subst ((i, t)::nil) tau).
Proof.
  intros.
  induction tau; mysimp.
  rewrite IHtau1.
  rewrite IHtau2.
  reflexivity.
Qed.

Hint Resolve ty_to_subst_single:core.
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

Hint Resolve ty_to_subst_schm:core.
Hint Rewrite ty_to_subst_schm:RE.


(** * Type instance definition **)

Definition is_schm_instance (tau : ty) (sigma : schm) :=
    exists (is_s : inst_subst), (apply_inst_subst is_s sigma) = (Some tau).

Lemma apply_inst_subst_gen_nth : forall (is_s : inst_subst) (i : id) (tau : ty),
    apply_inst_subst is_s (sc_gen i) = Some tau -> nth_error is_s i = Some tau.
Proof.
  intros.
  simpl in H.
  destruct (nth_error is_s i).
  inversion H. reflexivity.
  inversion H.
Qed.

Hint Resolve apply_inst_subst_gen_nth:core.
Hint Rewrite apply_inst_subst_gen_nth:RE.

(**  Most general instance definition **)
Definition most_general_schm_instance (tau : ty) (sigma : schm) :=
  is_schm_instance tau sigma -> forall tau', is_schm_instance tau' sigma ->
                                    exists (s : substitution), tau' = apply_subst s tau.

(** ** Application of a simple substitution over a inst_subst *)
Definition map_apply_subst_ty (s : substitution) (is_s : inst_subst) : inst_subst :=
  List.map (apply_subst s) is_s.

(** Some facts about application of a simple substitution over a inst_subst  *)
Lemma apply_inst_subst_con_inversion : forall (is_s : inst_subst) (e : schm) (i : id),
    e = sc_con i -> apply_inst_subst is_s e = Some (con i).
Proof.
  intros.
  subst.
  apply apply_inst_subst_con.
Qed.

Hint Resolve apply_inst_subst_con_inversion:core.
Hint Rewrite apply_inst_subst_con_inversion:RE.

Fixpoint find_instance (sigma : schm) (tau : ty) :=
  match sigma with
  | sc_con i => con i
  | sc_var i => var i
  | sc_gen st => tau
  | sc_arrow sigma1 sigma2 => arrow (find_instance sigma1 tau) (find_instance sigma2 tau)
  end.

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

Hint Resolve apply_inst_subst_succeeds:core.

Lemma apply_inst_subst_ge_app : forall (sigma : schm) (is_s l : inst_subst),
    max_gen_vars sigma <= length is_s -> apply_inst_subst (is_s ++ l) sigma = apply_inst_subst is_s sigma.
Proof.
  induction sigma; crush.
  erewrite IHsigma1; eauto.
  erewrite IHsigma2; eauto.
  apply Nat.max_lub_r in H.
  apply H.
  apply Nat.max_lub_l in H.
  apply H.
Qed.

Hint Resolve apply_inst_subst_ge_app:core.

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

Hint Resolve is_instance_le_max:core.

(** * Lemmas relation instance substitution and ty_to_schm *)

Lemma apply_inst_ty_to_schm : forall (tau : ty) (is_s : inst_subst),
    apply_inst_subst is_s (ty_to_schm tau) = Some tau.
Proof.
  intros.
  induction tau; mysimp.
  rewrite IHtau1.
  rewrite IHtau2.
  reflexivity.
Qed.

Hint Resolve apply_inst_ty_to_schm:core.
Hint Rewrite apply_inst_ty_to_schm:RE.

Lemma apply_subst_inst_to_ty_to_schm : forall (is_s : inst_subst) (tau : ty),
    apply_inst_subst is_s (ty_to_schm tau) = Some tau.
Proof.
  induction tau; crush.
Qed.

Hint Resolve apply_subst_inst_to_ty_to_schm:core.
Hint Rewrite apply_subst_inst_to_ty_to_schm:RE.

(** * Lemma relating map substitution and apply instance substitution *)

Lemma subst_inst_subst_type_var : forall (is_s : inst_subst) (s: substitution) (i : id),
    (apply_inst_subst is_s (sc_var i)) = (Some (var i)) ->
    (apply_inst_subst (map_apply_subst_ty s is_s) (apply_subst_schm s (sc_var i))) =
    (Some (apply_subst s (var i))).
Proof.
  induction is_s.
  simpl.
  - intros. induction s.
    + reflexivity.
    + mysimp.
  - intros. destruct s.
    + reflexivity.
    + erewrite <- apply_inst_ty_to_schm.
      fequals.
Qed.

Hint Resolve subst_inst_subst_type_var:core.
Hint Rewrite subst_inst_subst_type_var:RE.

Lemma nth_error_map_apply_subst : forall (is_s : inst_subst) (s : substitution) (i : id) (tau : ty),
    nth_error is_s i = Some tau ->
    nth_error (map_apply_subst_ty s is_s) i = Some (apply_subst s tau).
Proof.
  intros.
  apply map_nth_error.
  assumption.
Qed.

Hint Resolve nth_error_map_apply_subst:core.
Hint Rewrite nth_error_map_apply_subst:RE.

Lemma map_apply_subst_gen : forall (tau : ty) (s : substitution) (is_s : inst_subst) (i : id),
    apply_inst_subst is_s (sc_gen i) = Some tau ->
    apply_inst_subst (map_apply_subst_ty s is_s) (sc_gen i) = Some (apply_subst s tau).
Proof.
  induction tau;
    try (intros;
    apply apply_inst_subst_gen_nth in H as H';
    eapply nth_error_map_apply_subst in H';
    simpl;
    rewrite H';
    reflexivity).
Qed.

Hint Resolve map_apply_subst_gen:core.
Hint Rewrite map_apply_subst_gen:RE.


(** * Lemmas to derive existentials and equations from apply_inst_susbt *)

Lemma exist_arrow_apply_inst_arrow : forall (is_s : inst_subst) (sigma1 sigma2 : schm) (tau : ty),
    apply_inst_subst is_s (sc_arrow sigma1 sigma2) = Some tau -> exists tau1 tau2, tau = arrow tau1 tau2.
Proof.
  intros.
  simpl in H.
    destruct (apply_inst_subst is_s sigma1).
    destruct (apply_inst_subst is_s sigma2).
    inversion H.
    exists t t0.
    reflexivity.
    inversion H.
    inversion H.
Qed.

Hint Resolve exist_arrow_apply_inst_arrow:core.
Hint Rewrite exist_arrow_apply_inst_arrow:RE.

Lemma and_arrow_apply_inst_arrow : forall (sigma1 sigma2 : schm) (tau tau' : ty) (is_s : inst_subst),
    apply_inst_subst is_s (sc_arrow sigma1 sigma2) = Some (arrow tau tau') ->
    (apply_inst_subst is_s sigma1 = Some tau) /\ (apply_inst_subst is_s sigma2 = Some tau').
Proof.
  intros.
  split;
    try (simpl in H;
    destruct (apply_inst_subst is_s sigma1);
    destruct (apply_inst_subst is_s sigma2);
    inversion H; reflexivity;
    inversion H;
    inversion H).
Qed.

Hint Resolve and_arrow_apply_inst_arrow:core.
Hint Rewrite and_arrow_apply_inst_arrow:RE.

Lemma exist_arrow_apply_inst_arrow2 : forall (sigma1 sigma2 : schm) (tau : ty) (is_s : inst_subst),
    apply_inst_subst is_s (sc_arrow sigma1 sigma2) = Some tau ->
    exists tau1 tau2, (apply_inst_subst is_s sigma1 = Some tau1) /\ (apply_inst_subst is_s sigma2 = Some tau2) /\
                 arrow tau1 tau2 = tau.
Proof.
  intros.
  simpl in H.
    destruct (apply_inst_subst is_s sigma1); crush.
    destruct (apply_inst_subst is_s sigma2); crush.
Qed.

Hint Resolve exist_arrow_apply_inst_arrow2:core.

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

Hint Resolve var_is_not_instance_of_arrow:core.

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

Hint Resolve con_is_not_instance_of_arrow:core.

Lemma subst_inst_subst_type:
  forall (sigma : schm) (s: substitution) (is_s : inst_subst) (tau : ty),
    (apply_inst_subst is_s sigma) = (Some tau) ->
    (apply_inst_subst (map_apply_subst_ty s is_s) (apply_subst_schm s sigma)) =
    (Some (apply_subst s tau)).
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
    specialize IHsigma1 with (s:=s) (is_s:=is_s) (tau:=x).
    specialize IHsigma2 with (s:=s) (is_s:=is_s) (tau:=x0).
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

Hint Resolve subst_inst_subst_type:core.
Hint Rewrite subst_inst_subst_type:RE.


(** * Lemmas about FV_schm *)

Lemma FV_type_scheme_type_to_type_scheme : forall (tau : ty),
    (FV_schm (ty_to_schm tau)) = (ids_ty tau).
Proof.
  intros.
  induction tau; try reflexivity.
  simpl. rewrite IHtau1. rewrite IHtau2. reflexivity.
Qed.

Hint Resolve FV_type_scheme_type_to_type_scheme:core.
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

Hint Resolve not_in_FV_type_scheme:core.
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

Hint Resolve subst_schm_when_dom_s_disjoint_with_FV_schm:core.
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

Hint Resolve apply_schm_compose_equiv:core.
Hint Rewrite apply_schm_compose_equiv:RE.

Fixpoint compute_inst_subst (st : id) (n : nat) : list ty :=
  match n with
  | 0 => nil
  | S n' =>
    match compute_inst_subst (S st) n' with
    | l' => (var st :: l')
    end
  end.

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

Hint Resolve nth_error_compute_inst_Some:core.
Hint Rewrite nth_error_compute_inst_Some:RE.

Lemma nth_error_compute_inst_None' : forall i j, nth_error (compute_inst_subst j i) i = None.
Proof.
  induction i.
  - intros. reflexivity.
  - intros. simpl. auto.
Qed.

Hint Resolve nth_error_compute_inst_None':core.
Hint Rewrite nth_error_compute_inst_None':RE.

Lemma nth_error_None_None_cons : forall i (l : list ty) a, nth_error (a :: l) i = None -> nth_error l i = None.
Proof.
  induction i; intros. simpl in *. inversion H.
  simpl in *.
  induction l. reflexivity.
  eapply IHi.
  apply H.
Qed.

Hint Resolve nth_error_None_None_cons:core.
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

Hint Resolve nth_error_None_None:core.
Hint Rewrite nth_error_None_None:RE.

Lemma nth_error_None_None_S : forall k i j, nth_error (compute_inst_subst j k) i = None -> nth_error (compute_inst_subst (S j) k) i = None.
Proof.
  induction k; intros. simpl. auto.
  induction i. simpl in *. inversion H.
  simpl. auto.
Qed.

Hint Resolve nth_error_None_None_S:core.
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

Hint Resolve nth_error_compute_inst_None:core.
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

Hint Resolve not_in_domain_compute:core.
Hint Rewrite not_in_domain_compute:RE.

Lemma find_subst_some_apply_app_compute_subst : forall (is_s : inst_subst) (s : substitution) (st0 st1 : id),
       st0 < st1 -> apply_subst ((compute_subst st1 is_s) ++ s) (var st0) = apply_subst s (var st0).
Proof.
  induction is_s;
  crush.
Qed.

Hint Resolve find_subst_some_apply_app_compute_subst:core.
Hint Rewrite find_subst_some_apply_app_compute_subst:RE.

Lemma compute_subst_cons_rwt : forall (st : id) (tau : ty) (is_s : inst_subst),
    compute_subst st (tau :: is_s) = (st, tau) :: compute_subst (S st) is_s.
Proof.
  auto.
Qed.

Hint Resolve compute_subst_cons_rwt:core.
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

Hint Resolve find_subst_id_compute:core.
Hint Rewrite find_subst_id_compute:RE.

(** * Make constant inst subst and find inst subst *)

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

Hint Resolve nth_error_make_constant_inst_subst3:core.
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

Hint Resolve apply_subst_inst_make_constant_inst_subst:core.
Hint Resolve apply_subst_inst_make_constant_inst_subst:RE.

Lemma find_some_instance_of_some_sigma : forall (sigma : schm) (tau : ty),
    is_schm_instance (find_instance sigma tau) sigma.
Proof.
  intros.
  unfold is_schm_instance.
  exists (make_constant_inst_subst (max_gen_vars sigma) tau).
  auto.
Qed.

Hint Resolve find_some_instance_of_some_sigma:core.
Hint Rewrite find_some_instance_of_some_sigma:RE.

Lemma length_make_constant_inst_subst : forall (n : nat) (t : ty), length (make_constant_inst_subst n t) = n.
  induction n; crush.
Qed.

Hint Resolve length_make_constant_inst_subst:core.

(** Lemma about projections a type instance of an arrow. *)
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

Hint Resolve arrow_sigma_more_general_than_arrow:core.
Hint Resolve arrow_sigma_more_general_than_arrow:RE.
