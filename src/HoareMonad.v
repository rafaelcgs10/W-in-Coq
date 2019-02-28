Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import LibTactics.

Require Import Program.
Require Import List.

Section hoare_state_monad.

Variable st : Set.

Definition State (a : Set) : Type := st -> a * st.

Definition Pre : Type := st -> Prop.

Definition Post (a : Type) : Type := st -> a -> st -> Prop.

Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Type :=
forall i : sig (fun t : st => pre t), sig (fun anonymous : option (prod a st) => match anonymous with
                                                                    | Some (x, f) => post (proj1_sig i) x f
                                                                    | None => False
                                                                    end).
           
Definition top : Pre := fun st => True.

Program Definition ret (a : Set) : forall x,
    @HoareState top a (fun i y f => i = f /\ y = x) := fun x s => exist _ (Some (x, s)) _.

Program Definition bind : forall a b P1 P2 Q1 Q2,
  (@HoareState P1 a Q1) -> (forall (x : a), @HoareState (P2 x) b (Q2 x)) ->
  @HoareState (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2) b (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3) :=
  fun a b P1 P2 Q1 Q2 c1 c2 s1 => match c1 s1 as y with
                               | Some (x, s2) => c2 x s2
                               | None => None
                               end.
Next Obligation.
  eapply p0.
  cbv in Heq_y.
  destruct c1.
  destruct x0.
  - simpl in y.
    destruct p1.
    inversion Heq_y.
    subst.
    auto.
  - simpl in y. contradiction.
Defined.
Next Obligation.
Admitted.

Program Definition get : @HoareState top st (fun i x f => i = f /\ x = i) := fun s => exist _ (Some (s, s)) _.

Program Definition put (x : st) : @HoareState top unit (fun _ _ f => f = x) := fun  _ => exist _ (Some (tt, x)) _.

End hoare_state_monad.

(** Gives you a fresh variable *)
Program Definition fresh : @HoareState nat (@top nat) nat (fun i x f => S i = f /\ i = x) := fun n => exist _ (Some (n, S n)) _.

Infix ">>=" := bind (right associativity, at level 71).

Delimit Scope monad_scope with monad.
Open Scope monad_scope.

Notation "x <- m ; p" := (m >>= fun x => p)%monad
    (at level 68, right associativity,
     format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'") : monad_scope.
(*
Notation "m ; p" := (m >>> p)%monad
    (at level 68, right associativity,
     format "'[' '[' m ']' ; '//' '[' p ']' ']'") : monad_scope.
*)
Close Scope monad_scope.
Notation "'DO' m 'OD'" := (m)%monad (at level 69, format "DO  '[' m ']'  OD").

Program Definition getN := 
  DO
    n <- @get nat ;
    ret n
  OD.


Program Definition applyMH (A B : Set) pre1 pos1
        (fn : forall x : A, (@HoareState B pre1 B pos1)) (x : A) : @HoareState B pre1 B pos1 := 
  DO
    x' <- fn x ;
    ret x'
  OD.
Next Obligation.
  unfold top.
  split; auto.
Defined.
Next Obligation.
  remember (fn x) as HH.
  edestruct (fn x).
  simpl in y.
  destruct x1 in y.
  destruct p in y.
  destruct ((x' <- fn x; ret x')).

  edestruct (fn x).
  simpl in *.
  destruct x1.
  destruct p.
  simpl in *.

  apply fn in x.
  edestruct x.

  match l with
  | nil => ret nil
  | x::xs =>
    DO
      x' <- fn x ;
      ret (x'::nil)
    OD
   end.
Next Obligation.
