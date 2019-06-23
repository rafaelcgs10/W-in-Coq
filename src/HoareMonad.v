Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import LibTactics.

Require Import Program.
Require Import List.
Require Import SimpleTypes.
Require Import Occurs.
Require Import Subst.
Require Import Omega.

Section hoare_state_monad.

Variable st : Set.

Definition Pre : Type := st -> Prop.

Definition Post (a e : Type) : Type := st -> sum a e -> st -> Prop.

Program Definition HoareState  (e : Type) (pre : Pre) (a : Type) (post : Post a e) : Type :=
  forall i : sig (fun t : st => pre t), sig (fun anonymous : prod (sum a e) st =>
                                       match anonymous with
                                       | (x, f) => post (proj1_sig i) x f
                                       end).

Definition top : Pre := fun st => True.

Program Definition ret {e : Type} (a : Type) : forall x,
    @HoareState e top a (fun i y f => i = f /\ y = x) := fun x s => (x, s).


Program Definition bind : forall a b e P1 P2 Q1 Q2,
    (@HoareState e P1 a Q1) -> (forall (x : a), @HoareState e (P2 x) b (Q2 x)) ->
    @HoareState e (fun s1 => P1 s1 /\ forall x s2, match x as x' with
                                          | inl l => Q1 s1 x s2 -> P2 l s2
                                          | inr r => True
                                          end )
                b
                (fun s1 y s3 => exists x, exists s2, match x, y as xy with
                                        | inl l, inl _ => Q1 s1 x s2 /\ Q2 l s2 y s3
                                        | inr r, inr _ => Q1 s1 x s2
                                        | inr r, inl _ => False
                                        | inl l, inr r => Q2 l s2 y s3
                                        end) :=
  fun a b e P1 P2 Q1 Q2 c1 c2 s1 => match c1 s1 as y with
                                 | (x, s2) => match x with
                                             | inl l => c2 l s2
                                             | inr r => (inr r, s1)
                                             end
                                 end.
Next Obligation.
  specialize y with (x := inl l).
  simpl in *.
  apply y.
  cbv in Heq_y.
  destruct c1.
  destruct x.
  simpl in y.
  destruct s.
  inversion Heq_y.
  subst.
  auto.
  inversion Heq_y.
Defined.
Next Obligation.
  destruct (c2 l).
  destruct x.
  cbv in Heq_y.
  simpl in *.
  destruct c1.
  simpl in *.
  destruct x.
  destruct s3.
  inversion Heq_y.
  subst.
  exists (@inl a e a0).
  exists s4.
  destruct s.
  split; auto.
  auto.
  inversion Heq_y.
Defined.
Next Obligation.
  destruct c1.
  destruct x.
  simpl in *.
  destruct s.
  inversion Heq_y.
  inversion Heq_y.
  subst.
  exists (@inr a e e0).
  exists s0.
  auto.
Defined.

Program Definition failT {B : Type} (b : B) (A : Type) : @HoareState B top A (fun _ _ _ => True) := fun s => (inr b, s).

Program Definition get' {B : Type} : @HoareState B top st (fun i x f => i = f /\ x = inl i) := fun s => (_, s).
Next Obligation.
  left.
  auto.
Defined.

Program Definition put' {B : Set} (x : st) : @HoareState B top unit (fun _ _ f => f = x) := fun  _ => (inl tt, x).

End hoare_state_monad.

Infix ">>=" := bind (right associativity, at level 71).

Notation "x <- m ; p" := (m >>= fun x => p)
    (at level 68, right associativity,
     format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'").


(** * Failures of W *)

Inductive UnifyFailure : ty -> ty -> Set :=
| occ_fail  : forall v t, occurs v t -> UnifyFailure (var v) t
| occ_fail'  : forall v t, occurs v t -> UnifyFailure t (var v)
| diff_cons : forall n n', n <> n' -> UnifyFailure (con n) (con n')
| con_arrow   : forall n l r, UnifyFailure (con n) (arrow l r)
| arrow_con   : forall n l r, UnifyFailure (arrow l r) (con n)
| arrow_left  : forall l l' r r', UnifyFailure l l' -> UnifyFailure (arrow l r) (arrow l' r')
| arrow_right  : forall l l' r r' s, UnifyFailure (apply_subst s r) (apply_subst s r') ->
                                UnifyFailure (arrow l r) (arrow l' r') .

Hint Constructors UnifyFailure.

Inductive SubstFailure : Set :=
| substFail : SubstFailure.

Hint Constructors SubstFailure.

Inductive MissingVar : id ->  Set :=
| missingVar : forall i, MissingVar i.

Hint Constructors MissingVar.

Inductive InferFailure : Set :=
| SubstFailure' : SubstFailure -> InferFailure
| UnifyFailure' : forall t1 t2, UnifyFailure t1 t2 -> InferFailure
| MissingVar' : forall i, MissingVar i -> InferFailure.

Hint Constructors InferFailure.

Unset Implicit Arguments.

(** * Instance of Hoare Exception-Sate Monad *)
Definition Infer := @HoareState id InferFailure.
Definition get := @get' id InferFailure.
Definition put := @put' id InferFailure.
