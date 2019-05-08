(** * Auxiliary list of ids functions and lemmas *)

Set Implicit Arguments.

Require Import SimpleTypes.
Require Import Subst.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import LibTactics.
Require Import MyLtacs.
Require Import NthErrorTools.


(** * Check if a id is in a list *)

Fixpoint in_list_id (i : id) (l : list id) : bool:=
  match l with
  | nil => false
  | x::l' => if eq_id_dec x i then true else in_list_id i l'
  end.

(** * Lemmas about [in_list_id] *)

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
Hint Rewrite in_list_id_or_append:RE.

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
Hint Rewrite in_list_id_or_append_inversion:RE.

Lemma in_list_id_or_append_inversion_midle : forall x l1 l2 l3 l4,
    in_list_id x (l1 ++ l2 ++ l3 ++ l4) = true ->
    in_list_id x (l1 ++ l2 ++ l4) = true \/ in_list_id x (l1 ++ l3 ++ l4) = true.
Proof.
  intros.
  induction l1.
  - simpl in *.
    apply in_list_id_or_append_inversion in H.
    destruct H; eauto.
  - simpl in *.
    destruct (eq_id_dec a x); eauto.
Qed.

Hint Resolve in_list_id_or_append_inversion_midle.
Hint Rewrite in_list_id_or_append_inversion_midle:RE.

Lemma in_list_id_cons_true : forall x l a,
    in_list_id x l = true -> in_list_id x (a::l) = true.
Proof.
  intros.
  mysimp.
Qed.

Hint Resolve in_list_id_cons_true.
Hint Rewrite in_list_id_cons_true:RE.

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
Hint Rewrite in_list_id_cons_false:RE.

Lemma in_list_id_append_comm_true :
  forall x l1 l2, in_list_id x (l1 ++ l2) = true <->
             in_list_id x (l2 ++ l1) = true.
Proof.
  intros.
  split; intros;
  apply in_list_id_or_append;
  apply in_list_id_or_append_inversion in H;
  destruct H; mysimp.
Qed.

Hint Resolve in_list_id_append_comm_true.
Hint Rewrite in_list_id_append_comm_true:RELOOP.

Lemma in_list_id_append_comm_true2 :
  forall x l1 l2 l3, in_list_id x (l1 ++ l2 ++ l3) = true ->
             in_list_id x (l1 ++ l3 ++ l2) = true.
Proof.
  intros.
  apply in_list_id_or_append_inversion in H.
  destruct H.
  eauto.
  apply in_list_id_append_comm_true in H.
  eauto.
Qed.

Hint Resolve in_list_id_append_comm_true2.
Hint Rewrite in_list_id_append_comm_true2:RE.

Lemma in_list_id_append_comm_true3 :
  forall x l1 l2 l3, in_list_id x (l1 ++ l2 ++ l3) = true ->
             in_list_id x (l2 ++ l1 ++ l3) = true.
Proof.
  intros.
  apply in_list_id_or_append_inversion in H.
  destruct H.
  eauto.
  apply in_list_id_append_comm_true2.
  rewrite app_assoc.
  apply in_list_id_append_comm_true.
  eauto.
Qed.

Hint Resolve in_list_id_append_comm_true3.
Hint Rewrite in_list_id_append_comm_true3:RE.

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
Hint Rewrite in_list_id_append1:RE.

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
Hint Rewrite in_list_id_append2:RE.

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
Hint Rewrite in_list_id_and_append:RE.

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
Hint Rewrite in_list_id_and_append_inversion:RE.

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
Hint Rewrite in_list_id_append_comm_false:RE.

Lemma in_list_id_append_inversion1 :
  forall x l1 l2, in_list_id x (l1 ++ l2) = false ->
              in_list_id x l1 = false.
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl in *. destruct (eq_id_dec a x); intuition.
Qed.

Hint Resolve in_list_id_append_inversion1.
Hint Rewrite in_list_id_append_inversion1:RE.

Lemma in_list_id_append_inversion2 :
  forall x l1 l2, in_list_id x (l1 ++ l2) = false ->
              in_list_id x l2 = false.
Proof.
  induction l1.
  - intros. simpl in H. auto.
  - intros. apply IHl1.
    simpl in H.
    destruct (eq_id_dec a x); intuition.
Qed.

Hint Resolve in_list_id_append_inversion2.
Hint Rewrite in_list_id_append_inversion2:RE.

Lemma in_list_id_le_ex : forall l p i, (forall x : id, in_list_id x (p :: l) = true -> x < i) -> p < i.
Proof.
  intros.
  specialize H with (x:=p).
  simpl in H.
  destruct (eq_id_dec p p); intuition.
Qed.

Hint Resolve in_list_id_le_ex.

(** * Get the biggest element from a list of ids *)

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

(** * Some [max_list_ids] lemmas *)

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
Hint Rewrite max_list_ids'_eq:RE.

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
Hint Rewrite apply_subst_dom_false:RE.

(** * Get a list of [id] from a [ty] *)

Fixpoint ids_ty_aux (tau : ty) (g : list id) : list id :=
  match tau with
  | var i => if in_list_id i g then g else i::g
  | arrow l r => let g' := (ids_ty_aux l g) in (ids_ty_aux r g')
  | _ => nil
  end.

Definition ids_ty2 (tau tau' : ty) := ids_ty_aux tau' (ids_ty tau).

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
Hint Rewrite not_in_img:RE.

(** * Checks if index of an [id] is in a list *)

Fixpoint index_list_id_aux (count i : id) (l : list id) : option id :=
  match l with
  | nil => None
  | x::l' => if eq_id_dec x i then Some count else index_list_id_aux (S count) i l'
  end.

Definition index_list_id (i:id) (l:list id) := index_list_id_aux 0 i l.
 
(** * Many lemmas about [index_list_id] *)

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
Qed.

Hint Resolve index_aux_false.

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

