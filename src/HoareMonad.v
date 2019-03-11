Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import LibTactics.

Require Import Program.
Require Import List.
Require Import Omega.

Section hoare_state_monad.

Variable st : Set.

Definition State (a : Type) : Type := st -> a * st.

Definition Pre : Type := st -> Prop.

Definition Post (a : Type) : Type := st -> a -> st -> Prop.

Program Definition HoareState (pre : Pre) (a : Type) (post : Post a) : Type :=
forall i : sig (fun t : st => pre t), sig (fun anonymous : option (prod a st) => match anonymous with
                                                                    | Some (x, f) => post (proj1_sig i) x f
                                                                    | None => True
                                                                    end).
           
Definition top : Pre := fun st => True.

Program Definition ret (a : Type) : forall x,
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
  - simpl in y. inversion Heq_y.
Defined.
Next Obligation.
  destruct (c2 x).
  destruct x0.
  cbv in Heq_y.
  simpl in *.
  destruct p1.
  exists x s2.
  split;
  auto.
  destruct c1.
  destruct x0.
  destruct p1.
  simpl in *.
  inversion Heq_y.
  subst.
  auto.
  inversion Heq_y.
  simpl in *.
  auto.
Defined.

Check bind.

Program Definition failT (A : Type) : @HoareState top A (fun _ _ _ => True) := fun s => exist _ None _.

Program Definition get : @HoareState top st (fun i x f => i = f /\ x = i) := fun s => exist _ (Some (s, s)) _.

Program Definition put (x : st) : @HoareState top unit (fun _ _ f => f = x) := fun  _ => exist _ (Some (tt, x)) _.

End hoare_state_monad.


Infix ">>=" := bind (right associativity, at level 71).

Notation "x <- m ; p" := (m >>= fun x => p)
    (at level 68, right associativity,
     format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'").

Program Definition getN := 
    n <- @get nat ;
    ret n.


Program Definition applyMH (A B : Set) pre1 pos1
        (fn : forall x : A, (@HoareState B pre1 B pos1)) (x : A) : @HoareState B pre1 B pos1 := 
    x' <- fn x ;
    ret x'
  .
Next Obligation.
  unfold top.
  split; auto.
Defined.
Next Obligation.
  cbv.
  edestruct (fn x).
  destruct x1.
  simpl in *.
  destruct p.
  auto.
  simpl in y.
  auto.
Defined.

(*
Lemma toListPost : forall A B, forall (post : Post A B), A -> (@HoareState A pre1 B pos1)) -> Post A (list B).
  intros.
  unfold Post in *.
  intros.
  eapply X; auto.
Qed.
*)

(*
Program Fixpoint mapMH (A B : Set) pre1 pos1 pre2 pos2
        (fn : forall x : A, (@HoareState A (pre1 x) B (pos1 x))) (l : list A) : @HoareState A pre2 (list B) pos2 := 
  match l with
  | nil => ret nil
  | x::xs =>
    DO
      x' <- fn x ;
      xs' <- mapMH pos2 fn xs ;
      ret (x'::xs')
    OD
   end.
Next Obligation.
  unfold top.
  auto.
Defined.
Next Obligation.
  auto.
  unfold HoareState in fn.
  apply exist in H.
Abort.
 *)
