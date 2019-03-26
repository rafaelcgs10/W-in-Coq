Set Implicit Arguments.


Require Import Unify.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.

Require Import LibTactics.


(** Check if a id is in a list *)

Fixpoint in_list_id (i : id) (l : list id) : bool:=
  match l with
  | nil => false
  | x::l' => if eq_id_dec x i then true else in_list_id i l'
  end.

Lemma in_list_id_or_append : forall x l1 l2,
    in_list_id x l1 = true \/ in_list_id x l2 = true ->
    in_list_id x (l1 ++ l2) = true.
Proof.
  intros.
  induction l1.
  - simpl.
    destruct H. simpl in H. intuition.
    assumption.
  - mysimp.
    apply IHl1.
    left.
    simpl in H.
    destruct (eq_id_dec a x).
    intuition.
    assumption.
Qed.

Hint Resolve in_list_id_or_append.

Lemma in_list_id_or_append_inversion : forall x l1 l2,
    in_list_id x (l1 ++ l2) = true ->
    in_list_id x l1 = true \/ in_list_id x l2 = true.
Proof.
  intros.
  induction l1.
  - simpl in *.
    right. assumption.
  - simpl in *.
    destruct (eq_id_dec a x).
    left.
    reflexivity.
    auto.
Qed.

Hint Resolve in_list_id_or_append_inversion.

Lemma in_list_id_cons_true : forall x l a,
    in_list_id x l = true -> in_list_id x (a::l) = true.
Proof.
  intros.
  mysimp.
Qed.

Hint Resolve in_list_id_cons_true.

Lemma in_list_id_cons_false : forall x l a,
    in_list_id x (a::l) = false -> in_list_id x l = false.
  Proof.
  intros.
  simpl in H.
  destruct (eq_id_dec a x);
  mysimp.
  inversion H.
Qed.

Hint Resolve in_list_id_cons_false.

Lemma in_list_id_append_comm_true :
  forall x l1 l2, in_list_id x (l1 ++ l2) = true ->
             in_list_id x (l2 ++ l1) = true.
Proof.
  intros.
  apply in_list_id_or_append.
  apply in_list_id_or_append_inversion in H.
  destruct H; mysimp.
Qed.

Hint Resolve in_list_id_append_comm_true.

Lemma in_list_id_append1 :
  forall x l1 l2, in_list_id x l1 = true ->
             in_list_id x (l1 ++ l2) = true.
Proof.
  intros.
  apply in_list_id_or_append.
  left.
  auto.
Qed.

Hint Resolve in_list_id_append1.

Lemma in_list_id_append2 :
  forall x l1 l2, in_list_id x l2 = true ->
             in_list_id x (l1 ++ l2) = true.
Proof.
  intros.
  apply in_list_id_or_append.
  right.
  auto.
Qed.

Hint Resolve in_list_id_append2.

Lemma in_list_id_and_append : forall x l1 l2,
    in_list_id x l1 = false /\ in_list_id x l2 = false ->
    in_list_id x (l1 ++ l2) = false.
Proof.
  intros.
  induction l1; mysimp.
  - simpl in H. destruct (eq_id_dec x x); intuition.
  - apply IHl1.
    split.
    simpl in H. destruct (eq_id_dec a x); intuition.
    assumption.
Qed.

Hint Resolve in_list_id_and_append.

Lemma in_list_id_and_append_inversion : forall x l1 l2,
    in_list_id x (l1 ++ l2) = false ->
    in_list_id x l1 = false /\ in_list_id x l2 = false.
Proof.
  intros.
  induction l1; mysimp;
  try (simpl in H; destruct (eq_id_dec x x); intuition);
  try (destruct (eq_id_dec a x); intuition).
Qed.

Hint Resolve in_list_id_and_append_inversion.

Lemma in_list_id_append_comm_false :
  forall x l1 l2, in_list_id x (l1 ++ l2) = false ->
             in_list_id x (l2 ++ l1) = false.
Proof.
  intros.
  apply in_list_id_and_append.
  apply in_list_id_and_append_inversion in H.
  destruct H; mysimp.
Qed.

Hint Resolve in_list_id_append_comm_false.

Lemma in_list_id_append_inversion1 :
  forall x l1 l2, (in_list_id x (l1 ++ l2) = false ->
              in_list_id x l1 = false).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl in *. destruct (eq_id_dec a x); intuition.
Qed.

Hint Resolve in_list_id_append_inversion1.

Lemma in_list_id_append_inversion2 :
  forall x l1 l2, (in_list_id x (l1 ++ l2) = false ->
              in_list_id x l2 = false).
Proof.
  induction l1.
  - intros. simpl in H. auto.
  - intros. apply IHl1.
    simpl in H.
    destruct (eq_id_dec a x); intuition.
Qed.

Hint Resolve in_list_id_append_inversion2.

(** index of a id is in a list *)

Fixpoint index_list_id_aux (count i : id) (l : list id) : option id :=
  match l with
  | nil => None
  | x::l' => if eq_id_dec x i then Some count else index_list_id_aux (S count) i l'
  end.

Hint Resolve index_list_id_aux.

Definition index_list_id (i:id) (l:list id) := index_list_id_aux 0 i l.
  
Fixpoint ids_ty_aux (tau : ty) (g : list id) : list id :=
  match tau with
  | var i => if in_list_id i g then g else i::g
  | arrow l r => let g' := (ids_ty_aux l g) in (ids_ty_aux r g')
  | _ => nil
  end.

Definition ids_ty2 (tau tau' : ty) := ids_ty_aux tau' (ids_ty tau).

Definition max_list_ids' :
  forall (l : list id) (n : id), {m: id | (forall x, in_list_id x l = true -> x <= m) /\ n <= m}.
  refine (fix max_list_ids' (l : list id) (n : id) :
            {m: id | (forall x, in_list_id x l = true -> x <= m) /\ n <= m} := 
  match l with 
  | nil => exist _ n _
  | x::l' => match le_gt_dec x n with
            | left P1 => match max_list_ids' l' n with
                        | exist _ m H => exist _ m _
                        end
            | right P2 => match max_list_ids' l' x with
                        | exist _ m H => exist _ m _
                        end
            end
  end).
  split.
  intros.
  simpl in H.
  inversion H.
  omega.
  split.
  intros.
  simpl in H0.
  destruct (eq_id_dec x x0).
  omega.
  apply H in H0.
  assumption.
  destruct H.
  assumption.
  split.
  intros.
  simpl in H0.
  destruct (eq_id_dec x x0).
  omega.
  destruct H.
  apply H.
  assumption.
  destruct H.
  omega.
Qed.

Definition max_list_ids l := max_list_ids' l 0.

Lemma max_list_ids'_eq : forall a x x0 l P, a > x -> max_list_ids' l a = exist _ x0 P -> x0 < x -> a = x.
Proof.
  intros.
  induction l.
  destruct P.
  omega.
  destruct P.
  omega.
Qed.

Hint Resolve max_list_ids'_eq.

Lemma max_list_ids'_false : forall  x l x0 P,  max_list_ids' l x = exist _ x0 P -> x0 < x -> False.
Proof.
  intros.
  induction l.
  - simpl in H.
    omega.
  - simpl in H.
    destruct (le_gt_dec a x).
    auto.
    destruct P.
    omega.
    destruct P.
    omega.
Qed.

Hint Resolve max_list_ids'_false.

Lemma in_list_id_le_ex : forall l p i, (forall x : id, in_list_id x (p :: l) = true -> x < i) -> p < i.
Proof.
  intros.
  specialize H with (x:=p).
  simpl in H.
  destruct (eq_id_dec p p); intuition.
Qed.

Hint Resolve in_list_id_le_ex.

Definition max_ids (i1 i2 : id) : id := if le_gt_dec i1 i2 then i2 else i1.

Definition max_ids_dep: forall (i1 i2 : id),
    {j : id | i1 <= j /\ i2 <= j}.
refine (fix max_ids_dep i1 i2 : {j : id | i1 <= j /\ i2 <= j} :=
        match le_gt_dec i1 i2 with
          | left _ => exist _ i2 _
          | right _ => exist _ i1 _
        end).
  omega.
  omega.
Defined.

Lemma apply_subst_dom_false : forall i rho,
    in_list_id i (dom rho) = false -> apply_subst rho (var i) = var i.
Proof.
  intros.
  induction rho.
  - reflexivity.
  - destruct a.
    simpl in H.
    destruct (eq_id_dec i0 i).
    inversion H.
    mysimp.
Qed.

Hint Resolve apply_subst_dom_false.

Lemma not_in_img: forall (s: substitution) (st x: id),
    st <> x -> 
    in_list_id st (img_ids s) = false ->
    in_list_id st (ids_ty (apply_subst s (var x))) = false.
Proof.
  intros.
  induction s. 
  - simpl in |- *. intros. mysimp.
  - destruct a.
    simpl in |- *. intros.
    destruct (eq_id_dec i x).
    + unfold img_ids in H0. simpl in H0.
      apply in_list_id_and_append_inversion in H0; destruct H0; auto.
    + simpl in *. eapply IHs; eauto. 
      induction t; simpl in *; mysimp; eauto.
      cases (find_subst s x); simpl in *; eauto. 
      unfold img_ids in H0. simpl in H0.
      eauto.
      destruct (eq_id_dec x st);
      eauto.
      unfold img_ids in H0. simpl in H0.
      eauto.
      unfold img_ids in H0. simpl in H0.
      eauto.
Qed.

Hint Resolve not_in_img.