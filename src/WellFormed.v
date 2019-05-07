(** * Well Formedness Definitions 
    Here we define the concepts of well formed types, substitutions and constraints.
    We say that a type is well formed if all of its variables are in a variable context.
    Similarly, a constraint is well formed if all of its types are well formed.*)

Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import LibTactics.
Require Import Program.
Require Import SimpleTypes.
Require Import Subst.
Require Import Varctxt.
Require Import Occurs.
Require Import MyLtacs.

(** * Well formed defintion for types *)

Fixpoint wf_ty (C : varctxt) (t : ty) : Prop :=
  match t with
    | var v => member C v
    | con _ => True
    | arrow l r => wf_ty C l /\ wf_ty C r
  end.

(** ** Several lemmas about well formed types *)
Lemma wf_ty_cons : forall c a t, wf_ty c t -> wf_ty (a::c) t.
Proof.
  intros.
  induction t; crush.
Qed.

Hint Resolve wf_ty_cons.

Lemma wf_ty_app : forall c' c t, wf_ty c t -> wf_ty (c++c') t.
Proof.
  induction c; induction t; crush.
Qed.

Hint Resolve wf_ty_app.
      
Lemma wf_ty_app_comm : forall c c' t, wf_ty (c++c') t -> wf_ty (c'++c) t.
Proof.
  induction c'; crush.
  induction t; crush.
  apply member_app_comm in H.
  crush.
Qed.

(** ** Definition of two well formed types *)

Definition wf_tys (C : varctxt) (t1 t2 : ty)  : Prop := wf_ty C t1 /\ wf_ty C t2.

(** Suppose that a type t is well formed with respect to a variable context [C] and
    the variable [x] is free in [t],
    if we substitute [x] for [u] and [u] is well formed with respecto to [C - {x}],
    we get a type that is well formed with respect to [C - {x}].

    This is formalized by the lemma subst_remove. *)

Lemma subst_remove : forall t x ctx,
    wf_ty ctx t -> member ctx x ->
    forall u, wf_ty (remove x ctx) u ->
         wf_ty (remove x ctx) (apply_subst ((x, u)::nil) t).
Proof.
  induction t ; crush.
Qed.

Hint Resolve subst_remove.

(** More lemmas about well formed types *)
Lemma wf_ty_var : forall i C, member C i <-> wf_ty C (var i).
Proof.
  split;
  induction C; crush.
Qed.

Hint Resolve wf_ty_var.

Lemma wf_ty_var_false : forall i C, wf_ty (remove i C) (var i) -> False.
Proof.
  induction C; crush.
Qed.

Lemma subst_remove_single : forall a C t t0,
    wf_ty (remove a C) t -> wf_ty C t -> wf_ty C t0 ->
    wf_ty (remove a C) (apply_subst ((a, t0)::nil) t).
Proof.
  induction t; crush.
  apply member_remove_false in H. contradiction.
Qed.

Hint Resolve subst_remove_single.

Lemma wf_ty_cons_inversion : forall t i C, wf_ty C t -> wf_ty (i::C) t.
Proof.
  crush.
Qed. 

Hint Resolve wf_ty_cons_inversion.

Lemma wf_ty_remove_inversion : forall i C t, wf_ty (remove i C) t -> wf_ty C t.
Proof.
  induction t; crush.
Qed.

Hint Resolve wf_ty_remove_inversion.

Lemma wf_ty_remove_remove_comm : forall i j C t, wf_ty (remove i (remove j C)) t -> wf_ty (remove j (remove i C)) t.
Proof.
  induction t; crush.
Qed.

Hint Resolve wf_ty_remove_remove_comm.

Lemma wf_ty_remove_minus_inversion : forall s a C t, wf_ty (remove a (minus C (dom s))) t -> wf_ty (remove a C) t.
Proof.
  induction s; intros; mysimp; simpl in *; eauto.
Qed.

Lemma wf_ty_remove_minus_inversion2 : forall s a C t, wf_ty (remove a (minus C s)) t -> wf_ty (minus C s) t.
Proof.
  induction s; intros; mysimp; simpl in *; eauto.
Qed.

Lemma wf_ty_minus_inversion : forall s C t, wf_ty (minus C s) t -> wf_ty C t.
Proof.
  induction s; intros; mysimp; simpl in *; eauto.
Qed.

Lemma wf_ty_remove_remove : forall t C i j, wf_ty (remove i C) t -> wf_ty (remove j C) t -> wf_ty (remove i (remove j C)) t.
Proof.
  induction t.
  induction C; intros; eauto; mysimp; simpl in *; eauto.
  destruct (eq_id_dec j j); try contradiction; eauto.
  destruct (eq_id_dec j i0); try contradiction; eauto.
  simpl in H.
  destruct (eq_id_dec j i); subst; try contradiction; eauto.
  destruct (eq_id_dec i0 j); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec i0 i0); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec i0 i); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec a i0); subst; try contradiction; simpl in *; eauto.
  destruct (eq_id_dec a j); subst; try contradiction; simpl in *; eauto.
  intros. auto.
  intros.
  simpl in *.
  mysimp.
Qed.
  
Hint Resolve wf_ty_remove_remove.

Lemma wf_ty_remove_minus : forall s i C t, wf_ty (remove i C) t -> wf_ty (minus C (dom s)) t -> wf_ty (remove i (minus C (dom s))) t.
Proof.
  induction s; intros; eauto; mysimp; simpl in *; eauto.
Qed.

Hint Resolve wf_ty_remove_minus.

Lemma wf_ty_subst_not_in_dom : forall t s1 C, wf_ty (minus C (dom s1)) t -> apply_subst s1 t = t.
Proof.
  induction t; intros.
  - simpl in H.
    apply member_minus_find_subst in H.
    simpl. rewrite H.
    reflexivity.
  - reflexivity.
  - rewrite apply_subst_arrow.
    simpl in H. destructs H.
    fequals.
    eapply IHt1.
    apply H.
    eapply IHt2.
    apply H0.
Qed.


(** ** Relating occurs check and well formedness of types *)

Lemma occurs_wf_ty v C t : wf_ty C t -> ~ occurs v t -> wf_ty (remove v C) t.
Proof.
  induction t ; mysimp ; try tauto.
Qed.

Hint Resolve occurs_wf_ty.

(** * Definition of a well formed substitution. *)
(**
    A substitution is well formed if is empty or is substitution [(v,t)::s'], 
    where [v] is a variable and [t] a type, then we have that:

    1 - [v] is in a variable context [C],
    
    2 -  [t] is well formed in the variable context [C - {v}],

    3 -  [t] is well formed in the variable context [C - dom(s')],

    4 -  [s'] is well formed in respect to [C - {v}].

    The third restriction of the
    [wf_subst] is an addition to the original unification, which
    was necessary because of the essential lemma [substs_remove] for the termination proof.
 *)

Fixpoint wf_subst (C : varctxt) (s : substitution) : Prop :=
  match s with
  | nil => True
  | (v,t) :: s' => member C v /\ wf_ty (remove v C) t /\
                  wf_ty (minus C (dom s')) t /\ (wf_subst (remove v C) s') 
  end.

(** ** Several lemmas about well formed substitutions *)

Lemma wf_subst_remove_inversion : forall s i C, wf_subst (remove i C) s -> wf_subst C s.
Proof.
  induction s; crush.
  rewrite remove_comm in H2.
  eauto.
Qed.

Hint Resolve wf_subst_remove_inversion.

Lemma wf_subst_wf_ty_subst_var' : forall s C i,
    wf_subst C s ->
    wf_ty C (var i) ->
    wf_ty C  (apply_subst s (var i)).
Proof.
  induction s . intros ; simpl in *; mysimp.
  intros.
  destruct a.
  specialize IHs with (i := i).
  simpl in H.
  destructs H.
  simpl.
  destruct (eq_id_dec i0 i).
  - subst.
    eauto.
  -
  specialize IHs with (C := (C)).
  simpl in *.
  cases (find_subst s i);
   eauto.
Qed. 

Lemma wf_subst_wf_ty_subst : forall t s C,
    wf_subst C s ->
    wf_ty C t ->
    wf_ty C (apply_subst s t).
Proof.
  induction t; intros; mysimp.
  rewrite apply_subst_fold.
  apply wf_subst_wf_ty_subst_var'; auto.
  destruct H0.
  auto.
  destruct H0.
  auto.
Qed.


Lemma wf_subst_remove_comm : forall s C b a,
    wf_subst (remove a (remove b C)) s ->
    wf_subst (remove b (remove a C)) s.
Proof.
  induction s; intros; simpl in *; mysimp; eauto.
  assert ((remove b (remove a0 C)) = (remove a0 (remove b C))). {
    rewrite remove_comm. reflexivity. }
  rewrite H3. assumption.
  rewrite remove_comm. assumption.
  assert ((remove b (remove a0 C)) = (remove a0 (remove b C))). {
    rewrite remove_comm. reflexivity. }
  rewrite H3. assumption.
Qed.


Lemma wf_subst_remove_minus_inversion : forall B C s a,
    wf_subst (remove a (minus C B)) s -> wf_subst (remove a C) s.
Proof.
  induction B. intros; mysimp; simpl in *; eauto.
  intros.
  specialize IHB with (C := remove a0 C) (s := s) (a:= a).
  simpl in *.
  apply wf_subst_remove_comm in H.
  rewrite minus_remove in IHB.
  apply IHB in H.
  apply wf_subst_remove_inversion in H.
  assumption.
Qed.

Lemma substs_remove_var : forall s C i,
    wf_subst C s ->
    wf_ty C (var i) ->
    wf_ty (minus C (dom s)) (apply_subst s (var i)).
Proof.
  induction s . intros ; simpl in *; mysimp.
  intros.
  destruct a.
  specialize IHs with (i := i).
  simpl in H.
  destructs H.
  simpl.
  destruct (eq_id_dec i0 i).
  - subst.
    eauto.
  -
  specialize IHs with (C := (minus C [i0])).
  simpl in *.
  cases (find_subst s i).
  + rewrite minus_remove_dist2.
    eapply IHs.
    eauto.
    eauto.
  + rewrite minus_remove_dist2.
    eauto.
Qed.

(** The following lemma is essential for the termination proof 
    since it shows that the varctx (may) decrease after the substitution. *)
Lemma substs_remove : forall t s C,
    wf_subst C s ->
    wf_ty C t ->
    wf_ty (minus C (dom s)) (apply_subst s t).
Proof.
  induction t; intros; mysimp.
  rewrite apply_subst_fold.
  apply substs_remove_var; auto.
  destruct H0.
  auto.
  destruct H0.
  auto.
Qed.

Hint Resolve substs_remove wf_subst_wf_ty_subst.

Lemma wf_subst_not_in_dom_apply_subst_list : forall s2 s1 C,
    wf_subst (minus C (dom s1)) s2 -> apply_subst_list s2 s1 = s2. 
Proof.
  induction s2; intros.
  reflexivity.
  simpl. destruct a.
  simpl in H.
  destructs H.
  rewrite IHs2 with (C := remove i C).
  apply wf_ty_remove_inversion in H0.
  apply wf_ty_subst_not_in_dom in H0. 
  rewrite H0.
  reflexivity.
  rewrite minus_remove.
  assumption.
Qed.

(** The following lemma is also essential for the termination proof. 
    If [x] is a not used in substitution [s] and type [t], and type [t] 
    has no nothing to do with [s], then composing [s] with [(x,t)] is well formed.
*)
Lemma wf_subst_last (s : substitution) :
  forall x t C, wf_subst C s ->
           member (minus C (dom s)) x ->
           wf_ty (remove x (minus C (dom s))) t ->
           wf_subst C (compose_subst s [(x,t)]).
Proof.
  induction s ; simpl ; intros . mysimp. eauto.
  destruct a. destructs H.
  simpl in *. splits; eauto.
  induction t0; mysimp; simpl in *; eauto; mysimp; eauto.
  apply wf_ty_remove_inversion in H1. apply wf_ty_remove_minus_inversion in H1. assumption.
  induction t0; mysimp; simpl in *; eauto; mysimp; eauto.
  rewrite dom_dist_app. rewrite apply_subst_list_dom. simpl.
  rewrite minus_app_comm. simpl. eauto. 
  rewrite dom_dist_app. rewrite apply_subst_list_dom. simpl.
  rewrite minus_app_comm. simpl. eauto. 
  fold (compose_subst s [(x, t)]).
  eapply IHs with (C:= remove i C); eauto.
  rewrite minus_remove. auto.
  rewrite minus_remove. auto.
Qed.

Lemma arrowcons (A:Type) : forall (s1 s2:list A) x, s1 ++ x::s2 = (s1 ++ x::nil) ++ s2.
  intros ; rewrite app_ass ; auto.
Qed.

Lemma compose_cons : forall s1 s2 i t C,
    wf_subst C s1 -> wf_subst C ((i, t) :: s2) ->
    wf_subst C (compose_subst (compose_subst s1 [(i, t)]) s2) ->
    wf_subst C (compose_subst s1 ((i, t) :: s2)).
Proof.
  intros.
  unfold compose_subst in *.
  rewrite arrowcons.
  assert ((apply_subst_list s1 ((i, t) :: s2) ++ [(i, t)]) =
          apply_subst_list (apply_subst_list s1 [(i, t)] ++ [(i, t)]) s2).
  { induction s1. simpl in *. mysimp. erewrite wf_ty_subst_not_in_dom; eauto.
    destruct a. simpl in *. mysimp. erewrite <- IHs1; eauto. fequals. fequals.
    induction t0; mysimp; eauto. erewrite wf_ty_subst_not_in_dom; eauto. simpl in *.
    mysimp. fequals; eauto.
  } 
  rewrite H2.
  fold (compose_subst s1 [(i, t)]) .
  eauto.
Qed.

(**
    This last lemma is also essential for the termination proof. 
    It is a condintion to create a well formed composed substitution .
 *)
Lemma wf_subst_arrowend : forall s2 C s1,
    wf_subst C s1 ->
    wf_subst (minus C (dom s1)) s2 ->
    wf_subst C (compose_subst s1 s2).
Proof.
  induction s2 ; simpl ; intros. rewrite compose_subst_nil_r ; auto.
  destruct a. destructs H0.
  eapply compose_cons; eauto. simpl. splits; eauto.
  apply wf_ty_remove_minus_inversion in H1. assumption. eauto.
  rewrite minus_minus_comm in H2.
  apply wf_ty_minus_inversion in H2. assumption.
  apply wf_subst_remove_minus_inversion in H3.
  eauto.
  eapply IHs2.
  eapply wf_subst_last; eauto. 
  rewrite dom_dist_compose.
  rewrite minus_app_comm.
  simpl.
  eauto.
Qed.

Hint Resolve wf_subst_arrowend.

