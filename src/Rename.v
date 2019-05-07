(** * Renaming substitution
      This file contains the definition of renaming substitution and its lemmas.
      The renaming substitution is essential to the let case of the soundness proof
      of algorithm W.
    *)

Set Implicit Arguments.

Require Import Disjoints.
Require Import Sublist.
Require Import ListIds.
Require Import SimpleTypes.
Require Import Subst.
Require Import MyLtacs.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import LibTactics.

(** * Renaming substitution definition *)
Definition ren_subst := list (id * id).

(** ** Renaming substitution projections *)
Definition dom_ren (rho : ren_subst) : list id := List.map (@fst id id) rho.
Definition img_ren (rho : ren_subst) : list id := List.map (@snd id id) rho.

(** ** Renaming substitution application *)
Fixpoint apply_ren_subst (s : ren_subst) (t : id) : id :=
  match s with
    | nil => t
    | (i,j) :: s' => if eq_id_dec i t then j else apply_ren_subst s' t
  end.

(** Inductive definition that asserts that a given [ren_subst] is realy a renaming. *)
Inductive is_rename_subst : ren_subst ->  Prop :=
| is_rename_intro : forall r, (are_disjoints (dom_ren r) (img_ren r)) ->
                         (forall (x y: id),
                             (in_list_id x (dom_ren r)) = true ->  
                             (in_list_id y (dom_ren r)) = true ->
                             x <> y -> (apply_ren_subst r x) <> (apply_ren_subst r y)) ->
                         is_rename_subst r.

(** * Several lemmas about the renaming substitution *)

Lemma nil_is_rename_subst : is_rename_subst nil.
Proof.
  econstructor.
  intro. intros.
  simpl in H. inversion H.
  intros.
  simpl.
  destruct H.
  destruct H0.
  assumption.
Qed.

Lemma dom_ren_simpl : forall rho i j, dom_ren ((i, j)::rho) = i::dom_ren rho.
Proof.
  reflexivity.
Qed.

Lemma img_ren_simpl : forall rho i j, img_ren ((i, j)::rho) = j::img_ren rho.
Proof.
  reflexivity.
Qed.

Inductive renaming_of_not_concerned_with: 
  (ren_subst) -> (list id) -> (list id) -> (list id) -> Prop :=
| renaming_of_not_concerned_with_intro : forall (r:ren_subst) (l l1 l2: (list id)),
    (is_rename_subst r) ->
    (dom_ren r) = l ->
    (are_disjoints l1 (img_ren r)) ->
    (are_disjoints l2 (img_ren r)) ->
    (renaming_of_not_concerned_with r l l1 l2).

Lemma dom_img_rename_subst: forall r s, 
    (in_list_id s (dom_ren r))=true -> {y: id | (in_list_id y (img_ren r))=true /\
                                               (apply_ren_subst r s) = y}.
Proof.
  intros.
  induction r.
  - simpl in H. inversion H.
  - destruct a.
    simpl in H. simpl.
    destruct (eq_id_dec i s).
    + exists i0. 
      destruct (eq_id_dec i0 i0); intuition.
    + apply IHr in H.
      destruct H.
      exists x.
      destruct (eq_id_dec i0 x); intuition.
Qed.

Hint Resolve dom_img_rename_subst.

(** Finding this special renaming substitution is an essential step in the let case of the soundness proof*)
Definition compute_renaming : forall (i : id) (l l1 l2 : list id),
    (forall x, in_list_id x l = true -> x < i) -> (forall x, in_list_id x l1 = true -> x < i) ->
    (forall x, in_list_id x l2 = true -> x < i) ->
    {rho : ren_subst | is_rename_subst rho /\
                       dom_ren rho = l /\ (forall y, in_list_id y (img_ren rho) = true -> i <= y) /\
                       (forall x, in_list_id x (dom_ren rho) = true -> x < i) /\
                       are_disjoints l1 (img_ren rho) /\
                       are_disjoints l2 (img_ren rho)}.
  refine (fix compute_renaming i l l1 l2 p p1 p2 :
            {rho : ren_subst | is_rename_subst rho /\ dom_ren rho = l /\
                               (forall y, in_list_id y (img_ren rho) = true -> i <= y) /\
                               (forall x, in_list_id x (dom_ren rho) = true -> x < i) /\
                               are_disjoints l1 (img_ren rho) /\
                               are_disjoints l2 (img_ren rho)} := 
            match l as y return l = y -> _ with
            | nil => fun _ => exist _ nil _
            | p::l' => fun H => match (compute_renaming (S i) l' l1 l2 _ _ _) with
                            | exist _ rl H => exist _ ((p, i)::rl) _
                            end
            end _); try clear compute_renaming.
  - split.
    + apply nil_is_rename_subst.
    + split.
      * subst. reflexivity.
      * simpl. repeat split; intros; inversion H.
  - subst. intros. eapply Nat.lt_lt_succ_r in p0.
    apply p0.
    simpl.
    mysimp.
  - intros.  apply p1 in H0. omega.
  - intros.  apply p2 in H0. omega.
  - split.
    + destruct H, H1, H2, H3, H4.
      assert (are_disjoints (p :: dom_ren rl) (i :: img_ren rl)).
      {        
        destruct H.
        rewrite H0 in p0.
        apply in_list_id_le_ex in p0 as p0'.
        apply Nat.lt_neq in p0' as p0''.
        apply are_disjoints_cons.
        assumption.
        auto.
        cases (in_list_id p (img_ren r)).
        apply H2 in Eq.
        omega.
        reflexivity.
        cases (in_list_id i (dom_ren r)).
        specialize p0 with (x:= i).
        simpl in p0.
        destruct (eq_id_dec p i).
        omega.
        rewrite <- H1 in p0.
        intuition.
        reflexivity.
      }
      econstructor.
      * simpl.
        assumption.
      * intros.
        destruct H.
        simpl.
        destruct (eq_id_dec p y).
        { 
          rewrite e in *.
          simpl in H7.
          destruct (eq_id_dec y x).
          intuition.
          apply H3 in H7 as ine.
          apply dom_img_rename_subst in H7 as H7'.
          destruct H7', a.
          apply H2 in H11 as ine2.
          rewrite H12.
          omega.
        }
        {
          destruct (eq_id_dec p x).
          {
            simpl in H8.
            destruct (eq_id_dec p y); try omega.
            apply dom_img_rename_subst in H8 as H8'.
            destruct H8', a.
            apply H2 in H11.
            apply H3 in H8.
            omega.
          }
          {
            simpl in H7, H8.
            destruct (eq_id_dec p x); try omega.
            destruct (eq_id_dec p y); try omega.
            apply H10.
            assumption.
            assumption.
            assumption.
          }
        }
    + split.
      * destruct H, H1, H2, H3.
        subst.
        reflexivity.
      * repeat split.
        {
          intros.
          destruct H, H2, H3, H4.
          simpl in H1.
          destruct (eq_id_dec i y).
          omega.
          apply H3 in H1.
          omega.
        }
        {
          intros.
          rewrite H0 in p0.
          simpl in H1.
          destruct (eq_id_dec p x).
          apply p0.
          subst. mysimp.
          apply p0.
          mysimp.
        }
        {
          destruct H, H1, H2, H3, H4.
          simpl.
          intro. intros.
          simpl.
          destruct (eq_id_dec i x).
          specialize p1 with (x:=x).
          rewrite e in *.
          intuition.
          unfold are_disjoints in H4.
          auto.
        }
        {
          destruct H, H1, H2, H3, H4.
          simpl.
          intro. intros.
          simpl.
          destruct (eq_id_dec i x).
          specialize p2 with (x:=x).
          rewrite e in *.
          intuition.
          unfold are_disjoints in H5.
          auto.
        }
  -  reflexivity.
Defined.

Hint Resolve compute_renaming.

Lemma exists_renaming_not_concerned_with: forall (l l1 l2: (list id)),
  {r:ren_subst | (renaming_of_not_concerned_with r l l1 l2)}.
Proof.
  intros.
  pose proof (max_list_ids l) as maxl.
  pose proof (max_list_ids l1) as maxl1.
  pose proof (max_list_ids l2) as maxl2.
  destruct maxl as [m1  Hm1], maxl1 as [m2 Hm2], maxl2 as [m3 Hm3].
  pose proof (max_ids_dep m2 m3) as mis2.
  destruct mis2 as [mi2].
  pose proof (max_ids_dep m1 mi2) as mis1.
  destruct mis1 as [mi1].
  destruct a, a0.
  destruct Hm1, Hm2, Hm3.
  sort.
  assert (forall n m p, n <= m /\ m <= p -> n <= p) as le_trans.
  {intros. omega. }
  assert (m2 <= mi1).
  {eapply le_trans. split. apply H. assumption. }
  assert (m3 <= mi1).
  {eapply le_trans. split. apply H0. assumption. }
  assert (forall n m, n <= m -> n < S m) as le_to_lt.
  {intros. omega. }
  assert (forall x : id, in_list_id x l = true -> x < S mi1).
  {intros. apply le_to_lt. eapply le_trans. split. apply H3.
   apply H11. apply H1. }
  assert (forall x : id, in_list_id x l1 = true -> x < S mi1).
  {intros. apply le_to_lt. eapply le_trans. split. apply H5. assumption. assumption. }
  assert (forall x : id, in_list_id x l2 = true -> x < S mi1).
  {intros. apply le_to_lt. eapply le_trans. split. apply H7. assumption. assumption. }
  pose proof (compute_renaming l l1 l2 H11 H12 H13) as COMP.
  inversion COMP.
  destruct H14.
  exists (x).
  econstructor.
  assumption.
  destruct H15.
  assumption.
  destruct H15, H16, H17, H18.
  assumption.
  destruct H15, H16, H17, H18.
  assumption.
Defined.

Hint Resolve exists_renaming_not_concerned_with.

Lemma index_rename_aux : forall (rho: ren_subst) (i: id) (l: (list id)) (c : id),
    is_rename_subst rho -> is_sublist_id l (dom_ren rho) -> in_list_id i (dom_ren rho) = true ->
    index_list_id_aux c i l =
    index_list_id_aux c (apply_ren_subst rho i) (List.map (apply_ren_subst rho) l).
Proof.
  induction l;
    intros.
  - reflexivity.
  - destruct (eq_id_dec a i).
    + subst.
      simpl. mysimp.
    + apply sublist_cons in H0 as H2.
      inversion H.
      inversion H0.
      inversion H2. 
      simpl. destruct (eq_id_dec a i); try contradiction.
      assert (apply_ren_subst rho a <> apply_ren_subst rho i).
      {apply H4; auto. apply H6. mysimp. } 
      mysimp.
Qed.

Hint Resolve index_rename_aux.

Lemma index_rename : forall (rho : ren_subst) (i : id) (l: (list id)),
    is_rename_subst rho ->
    is_sublist_id l (dom_ren rho) ->
    in_list_id i (dom_ren rho) = true ->
    index_list_id i l = index_list_id (apply_ren_subst rho i) (List.map (apply_ren_subst rho) l).
Proof.
  intros.
  unfold index_list_id.
  apply index_rename_aux; auto.
Qed.

Hint Resolve index_rename.

(** For some l disjoint with img_ren rho, apply_ren_subst rho i is not in l*)
Lemma rename_img : forall (i : id) (rho : ren_subst) (l: list id),
    (is_rename_subst rho) -> (are_disjoints l (img_ren rho)) ->
    (in_list_id i (dom_ren rho)) = true ->
    (in_list_id (apply_ren_subst rho i) l) = false.
Proof.
  intros.
  inversion H.
  apply H2 in H1 as H1'.
  pose proof dom_img_rename_subst rho i H1 as H5.
  destruct H5, a.
  rewrite H6.
  eapply disjoint_inversion2.
  apply H0.
  auto.
Qed.

Hint Resolve rename_img.

Lemma in_list_id_dom_img : forall rho i, 
    (in_list_id i (dom_ren rho) = true ->
     in_list_id (apply_ren_subst rho i) (img_ren rho) = true).
Proof.
  induction rho.
  intros.
  - inversion H.
  - destruct a. 
    intros.
    simpl in *. destruct (eq_id_dec i0 i); intros; simpl in *; mysimp. 
Qed.

Hint Resolve in_list_id_dom_img.

(** ** Converts a renaming substitute to a usual substitution *)

Fixpoint rename_to_subst (r: ren_subst): substitution :=
  match r with
  | nil => nil
  | vt:: l => ((fst vt), (var (snd vt)))::(rename_to_subst l)
  end.

(** ** Some lemmas about the above conversion *)

Lemma dom_rename_to_subst : forall rho,  (dom (rename_to_subst rho) = dom_ren rho).
Proof.
  intros.
  induction rho.
  - reflexivity.
  - simpl.
    rewrite IHrho.
    reflexivity.
Qed.

(**  A lemma about apply a renaminng substitution *)
Lemma apply_subst_rename_to_subst : forall rho i,
    are_disjoints (dom_ren rho) (img_ren rho) ->
    apply_subst (rename_to_subst rho) (var i) = var (apply_ren_subst rho i).
Proof.
  induction rho; intros.
  - reflexivity.
  - destruct a.
    assert (in_list_id i1 (dom_ren ((i0, i1)::rho)) = false).
    { eapply disjoint_inversion2. apply H. mysimp. }
    rewrite <- dom_rename_to_subst in H0.
    simpl in H0.
    destruct (eq_id_dec i0 i1).
    inversion H0.
    apply apply_subst_dom_false in H0.
    simpl. 
    destruct (eq_id_dec i0 i).
    auto.
    fold (apply_subst (rename_to_subst rho) (var i)).
    apply IHrho.
    eapply are_disjoints_cons_inversion.
    apply H.
Qed.

Hint Resolve apply_subst_rename_to_subst.