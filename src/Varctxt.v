(** * The context of type variables 
      This file contains the defintion of variable context [varctxt],
      its auxiliary functions and several lemmas about them.
    *)

Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.
Require Import LibTactics.
Require Import SimpleTypes.
Require Import Subst.
Require Import MyLtacs.
Import ListNotations.


(** Type variables context is the key element to the formalization of the termination
    argument of the unification algorithm. This context is used to store the variables
    that aren't yet solved by the unification. At each step, the unification algorithm
    will solve some variables (thus, the size of the context decreases), or the measure
    of constraints being unified deacreses. *)

Definition varctxt := list id.

(** Definition of when a variable (id) is member of a variable context *)

Fixpoint member (C : varctxt) (i : id) : Prop :=
  match C with
    | nil => False
    | v :: vs => if eq_id_dec v i then True else member vs i
  end.

Lemma member_app : forall c c' i, member c i -> member (c++c') i.
Proof.
  induction c; crush.
Qed.

Hint Resolve member_app.

Lemma member_app2 : forall c c' i, member c' i -> member (c++c') i.
Proof.
  induction c; crush.
Qed.

Hint Resolve member_app2.

(** Decidability of the previous membership relation *)

Definition member_dec : forall C i, {member C i} + {~ member C i}.
  refine (fix member_dec (C : varctxt) (i : id) : {member C i} + {~ member C i} :=
                match C with
                  | nil => right _ _
                  | v :: vs =>
                      match eq_id_dec v i with
                        | left _ => left _ _
                        | right _ =>
                            match member_dec vs i with
                              | left _ => left _ _
                              | right _ => right _ _
                            end
                      end
                end) ; mysimp.
Defined.

Lemma member_app_or : forall c c' i, member (c++c') i -> member c i \/ member c' i.
Proof.
  intros.
  induction c; crush.
Qed.

Hint Resolve member_app_or.

Lemma member_or_app : forall c c' i, member c i \/ member c' i <-> member (c++c') i.
Proof.
  split; crush.
Qed.

Hint Resolve member_or_app.

Lemma member_app_comm : forall c c' i, member (c'++c) i -> member (c++c') i.
Proof.
  intros.
  apply member_or_app in H; crush.
Qed.

Hint Resolve member_app_comm.

(** Removing a variable from a variable context *)

Fixpoint remove (v : id) (ctx : varctxt) : varctxt :=
  match ctx with
    | nil => nil
    | y :: ys => if eq_id_dec y v then remove v ys else y :: (remove v ys)
  end.

Lemma remove_nil : forall i, remove i [] = [].
Proof.
  crush.
Qed.

Hint Resolve remove_nil.
Hint Rewrite remove_nil.

Lemma remove_diff_member : forall x t ctx, member ctx t -> x <> t -> member (remove x ctx) t.
Proof.
  induction ctx ; crush.
Qed.

Hint Resolve remove_diff_member.

Lemma remove_comm : forall x y C, remove x (remove y C) = remove y (remove x C).
Proof.
  induction C ; crush.
Qed.

Hint Resolve remove_comm.
Hint Rewrite remove_comm:RELOOP.

(** Removing a list of names from a given variable context. *)

Fixpoint minus (C : varctxt) (xs : list id) : varctxt :=
  match xs with
    | nil => C
    | x :: xs => remove x (minus C xs)
  end.


Lemma minus_remove : forall (C2 C1 : varctxt) (x : id), minus (remove x C1) C2 = remove x (minus C1 C2).
Proof.
  induction C2; crush.
Qed.

Hint Resolve minus_remove.
Hint Rewrite minus_remove:RE.

Lemma minus_arrow : forall (C : varctxt) s v t, minus C (dom (s ++ (v,t) :: nil)) = remove v (minus C (dom s)).
Proof.
  induction s ; crush. 
Qed.

Hint Resolve minus_arrow.
Hint Rewrite minus_arrow:RE.

Lemma member_remove_false : forall i C, member (remove i C) i -> False.
Proof.
  induction C; crush.
Qed.

Hint Resolve member_remove_false.

Lemma member_diff_inversion : forall a i0 C, a <> i0 -> member (a :: C) i0 -> member C i0.
Proof.
  crush.
Qed.

Hint Resolve member_diff_inversion.

Lemma member_remove_inversion : forall i i0 C, member (remove i C) i0 -> member C i0.
Proof.
  induction C;
  crush.
Qed.

Hint Resolve member_diff_inversion member_remove_inversion.

Lemma member_remove_remove_comm : forall C i j k, member (remove i (remove j C)) k -> member (remove j (remove i C)) k.
Proof.
  induction C; crush.
Qed.

Hint Resolve member_remove_remove_comm.

Lemma member_minus_remove : forall a C i0 i, member (minus (remove i0 C) a) i -> member (remove i0 (minus C a)) i.
Proof.
  induction a; crush.
Qed.

Hint Resolve member_minus_remove.

Lemma minus_nil1 : forall l, minus nil l = nil.
Proof.
  intros.
  induction l; mysimp.
  rewrite IHl. reflexivity.
Qed.
    
Hint Resolve minus_nil1.
Hint Rewrite minus_nil1:RE.

Lemma minus_nil2 : forall l, minus l nil = l.
Proof.
  intros.
  reflexivity.
Qed.

Hint Resolve minus_nil2.
Hint Rewrite minus_nil2:RE.

Lemma non_member_remove_length : forall C v, ~ member C v -> length (remove v C) = length C.
Proof.
  induction C ; auto ; mysimp ; intros ; mysimp ; try tauto.
Qed.

Lemma minus_dist_r : forall l l1 l2, (minus l (l1 ++ l2) = minus (minus l l1) l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl.
    rewrite IHl1.
    rewrite minus_remove.
    reflexivity.
Qed.

Lemma remove_remove_inversion : forall a i, remove i (remove i a) = (remove i a).
Proof.
  intros.
  induction a.
  reflexivity.
  simpl.
  destruct (eq_id_dec a i).
  assumption.
  simpl.
  destruct (eq_id_dec a i); intuition.
  rewrite IHa.
  reflexivity.
Qed.

Lemma minus_remove_dist1 : forall i a b, remove i (minus a b) = minus (remove i a) (remove i b).
Proof.
  intros.
  induction b.
  - reflexivity.
  - simpl in *.
    destruct (eq_id_dec a0 i).
    subst.
    rewrite <- IHb.
    rewrite remove_remove_inversion.
    reflexivity.
    simpl in *.
    rewrite remove_comm.
    fequals.
Defined.

Lemma minus_remove_dist2 : forall i a b, remove i (minus a b) = minus (remove i a) b.
Proof.
  intros.
  induction b.
  - reflexivity.
  - simpl in *.
    rewrite <- IHb.
    rewrite remove_comm.
    reflexivity.
Defined.

Lemma len_remove_le : forall C i, length (remove i C) <= length C.
Proof.
  intros.
  induction C; simpl; auto.
  destruct (eq_id_dec a i). omega.
  simpl. omega.
Qed.

Lemma len_remove_le_S : forall C i, length (remove i C) <= S (length C).
Proof.
  intros.
  induction C; simpl; auto.
  destruct (eq_id_dec a i). omega.
  simpl. omega.
Qed.

Lemma len_minus_le : forall C a, length (minus C a) <= length C.
Proof.
    induction a.
    + simpl. auto.
    + simpl. 
      rewrite len_remove_le.
      assumption.
Qed.

Lemma not_member_remove : forall i a, ~ (member a i) -> remove i a = a.
Proof.
  intros.
  induction a.
  - reflexivity.
  - simpl in *. destruct (eq_id_dec a i).
    intuition.
    erewrite IHa; auto.
Qed.

Lemma member_not_member : forall C a i, member C i -> ~(member a i) -> member (minus C a) i.
Proof.
  intros.
  induction a.
  - simpl. assumption.
  - simpl in *.
    destruct (eq_id_dec a i); intuition.
Qed.

Hint Resolve member_not_member.

Lemma len_not_member_remove : forall i a, ~(member a i) -> length a = length (remove i a).
Proof.
  intros.
  induction a; auto.
  simpl in *.
  destruct (eq_id_dec a i); intuition.
  simpl. congruence.
Qed.

Lemma aux''' : forall  (a: list id) i,  length (remove i a) <= length a.
Proof.
  induction a; intros; mysimp.
Qed.

Lemma aux'' : forall  (b a: list id) i, length b < length a -> length (remove i b) < length a.
  intros.
  pose proof (aux''' b i).
  apply Nat.lt_eq_cases in H0.
  destruct H0.
  omega.
  omega.
Qed.

Lemma member_minus_find_subst : forall s C i, member (minus C (dom s)) i -> find_subst s i = None.
Proof.
  induction s; intros; simpl in *; eauto; mysimp; simpl in *.
  apply member_remove_false in H. contradiction.
  specialize IHs with (C := remove a C).
  apply IHs.
  rewrite minus_remove. auto.
Qed.

Lemma member_minus_inversion : forall a C i, member (minus C a) i -> member C i.
Proof.
  induction a; intros; simpl in *; mysimp.
  eauto.
Qed.

Hint Resolve member_minus_inversion.

Lemma minus_minus_comm : forall A B C, minus (minus C A) B = minus (minus C B) A.
Proof.
  induction A. intros; repeat rewrite minus_nil2. reflexivity.
  intros.
  simpl.
  rewrite minus_remove.
  fequals.
Qed.

Lemma  minus_app_comm_cons : forall l1 l2 l a, minus l (l1 ++ a::l2) = minus l (a::l1 ++ l2).
Proof. 
  induction l1; intros. reflexivity.
  simpl.
  rewrite remove_comm.
  fequals.
  rewrite IHl1.
  simpl. reflexivity.
Qed.

Lemma  minus_app_comm : forall l1 l2 l, minus l (l1 ++ l2) = minus l (l2 ++ l1).
Proof.
  induction l1. intros. simpl. rewrite app_nil_r. reflexivity.
  intros.
  rewrite minus_app_comm_cons. simpl.
  rewrite IHl1. reflexivity.
Qed.

Lemma remove_varctxt_length : forall C v, member C v -> length (remove v C) < length C.
Proof.
  intros ; induction C ; simpl in * ; try contradiction ; mysimp ;
  destruct (member_dec C v) ; auto with arith ;
   match goal with
     | [H : ~ member _ _ |- _] => rewrite (non_member_remove_length _ _ H) ; auto with arith
   end.
Qed.

Hint Resolve remove_varctxt_length.

Lemma member_len_remove_minus' : forall C i a, member C i -> ~(member a i) -> length (remove i (minus C a)) < length (minus C a).
Proof.
  intros.
  apply remove_varctxt_length; eauto.
Qed.

Lemma member_len_minus_lt : forall s C i, member C i -> length (minus C (i::s)) < length C.
Proof.
  induction s; intros.
  - simpl in *. apply remove_varctxt_length. auto. 
  - simpl in *.
    apply IHs in H.
    destruct (eq_id_dec a i).
    + subst.
      rewrite remove_remove_inversion.
      assumption.
    + rewrite remove_comm. eapply aux''. auto.
Qed.

Hint Resolve member_len_minus_lt. 

