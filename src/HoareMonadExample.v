Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Program.
Require Import Omega.

Section hoare_state_monad.

Variable st : Set.

Definition Pre : Type := st -> Prop.

Definition Post (a : Type) : Type := st -> a -> st -> Prop.

Program Definition HoareState (pre : Pre) (a : Type) (post : Post a) : Type :=
  forall i : {t : st | pre t}, {(x, f) : a * st | post i x f}.

Definition top : Pre := fun st => True.

Program Definition ret (a : Type) : forall x,
    @HoareState top a (fun i y f => i = f /\ y = x) := fun x s => (x, s).

Program Definition bind : forall a b P1 P2 Q1 Q2,
    (@HoareState P1 a Q1) -> (forall (x : a), @HoareState (P2 x) b (Q2 x)) ->
    @HoareState (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
                b
                (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3) :=
                 fun a b P1 P2 Q1 Q2 c1 c2 s1 => match c1 s1 as y with
                                 | (x, s2) => c2 x s2
                                 end.
Next Obligation.
  eapply p0.
  cbv in Heq_y.
  destruct c1.
  destruct x0.
  simpl in y.
  inversion Heq_y.
  subst.
  auto.
Defined.
Next Obligation.
  destruct (c2 x).
  destruct x0.
  cbv in Heq_y.
  simpl in *.
  destruct c1.
  destruct x0.
  simpl in *.
  inversion Heq_y.
  subst.
  exists a0. exists s0.
  split;
    auto.
Defined.

Check bind.

Program Definition get : @HoareState top st (fun i x f => i = f /\ x = i) := fun s => (s, s).

Program Definition put (x : st) : @HoareState top unit (fun _ _ f => f = x) := fun  _ => (tt, x).

End hoare_state_monad.

Infix ">>=" := bind (right associativity, at level 71).

Notation "x <- m ; p" := (m >>= fun x => p)
    (at level 68, right associativity,
     format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'").

Inductive TreeNat : Type :=
| Leaf : nat -> TreeNat 
| Node : TreeNat -> TreeNat -> TreeNat.

Inductive NewNumberTree : TreeNat -> nat -> Prop :=
| LeafNew : forall n1 n2, n1 < n2 ->
                     NewNumberTree (Leaf n1) n2
| NodeNew : forall t1 t2 n, NewNumberTree t1 n ->
                       NewNumberTree t2 n ->
                       NewNumberTree (Node t1 t2) n.

Lemma new_number_trans_le : forall n1 n2 t, NewNumberTree t n1 ->
                                       n1 <= n2 ->
                                       NewNumberTree t n2.
Proof.
  intros.
  induction H.
  econstructor; omega.
  econstructor; auto.
Qed.

Hint Resolve new_number_trans_le:core.

Unset Implicit Arguments.

Program Fixpoint change_zeros (t : TreeNat) (n : nat) :
  NewNumberTree t n -> {(t', n') : TreeNat * nat | NewNumberTree t' n' /\ n <= n'} :=
  fun pre => 
  match t with
  | Leaf 0 =>  exist _ (Leaf n, S n) _
  | Leaf n' => exist _ (Leaf n', n) _
  | Node t1 t2 => match change_zeros t1 n _ with
                 | (t1', n') => match change_zeros t2 n' _ with
                               | (t2', n'') => exist _ (Node t1' t2', n'') _
                               end
                 end
  end.
Next Obligation.
  split;
  econstructor; auto.
Defined.
Next Obligation.
  inversion pre. subst.
  auto.
Defined.
Next Obligation.
  inversion pre.
  subst.
  eauto.
Defined.
Next Obligation.
  split.
  - econstructor; eauto.
  - omega.
Defined.

Program Definition fresh : @HoareState nat (@top nat) nat (fun i x f => S i = f /\ i = x) := fun n => (n, S n).

Unset Implicit Arguments.

Program Fixpoint change_zeros_m (t : TreeNat) :
  @HoareState nat (fun i => NewNumberTree t i) TreeNat (fun i t' f => (NewNumberTree t' f) /\ i <= f) := 
  match t with
  | Leaf 0 =>
           n' <- fresh ;
           ret (Leaf n')
  | Leaf n' => ret (Leaf n')
  | Node t1 t2 =>
               t1' <- change_zeros_m t1 ; 
               t2' <- change_zeros_m t2 ; 
               ret (Node t1' t2')
  end.
Next Obligation.
  unfold top; split; eauto.
Defined.
Next Obligation.
  split; eauto.
  inversion H.
  subst.
  econstructor; eauto.
Defined.
Next Obligation.
  unfold top; eauto.
Defined.
Next Obligation.
  split; inversion H; subst; eauto.
  intros.
  destruct H0.
  split; intros; eauto.
  unfold top.
  auto.
Defined.
Next Obligation.
  destruct (change_zeros_m t1 >>= _).
  simpl in *.
  destruct x0.
  destruct y.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H3.
  subst.
  split; eauto.
  econstructor; eauto.
  omega.
Defined.
  
