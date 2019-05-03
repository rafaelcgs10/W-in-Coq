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

Definition State (a : Type) : Type := st -> a * st.

Definition Pre : Type := st -> Prop.

Definition Post (a : Type) : Type := st -> a -> st -> Prop.

Program Definition HoareState  (B : Prop) (pre : Pre) (a : Type) (post : Post a) : Type :=
forall i : sig (fun t : st => pre t), sig (fun anonymous : sumor (prod a st) B => match anonymous with
                                                                    | inleft (x, f) => post (proj1_sig i) x f
                                                                    | inright _ => B
                                                                    end).
           
Definition top : Pre := fun st => True.

Program Definition ret {B : Prop} (a : Type) : forall x,
    @HoareState B top a (fun i y f => i = f /\ y = x) := fun x s => exist _ (inleft (x, s)) _.


Program Definition bind : forall a b P1 P2 Q1 Q2 B,
  (@HoareState B P1 a Q1) -> (forall (x : a), @HoareState B (P2 x) b (Q2 x)) ->
  @HoareState B (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2) b (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3) :=
  fun B a b P1 P2 Q1 Q2 c1 c2 s1 => match c1 s1 as y with
                               | inleft (x, s2) => c2 x s2
                               | inright R => inright R
                               end.
Next Obligation.
  eapply p.
  cbv in Heq_y.
  destruct c1.
  destruct x0.
  - simpl in y.
    destruct p0.
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
  destruct p0.
  exists x s2.
  split;
  auto.
  destruct c1.
  destruct x0.
  destruct p0.
  simpl in *.
  inversion Heq_y.
  subst.
  auto.
  inversion Heq_y.
  simpl in *.
  auto.
Defined.

Check bind.

Program Definition failT {B : Prop} (b : B) (A : Type) : @HoareState B top A (fun _ _ _ => True) := fun s => exist _ (inright b) _.

Program Definition get' {B : Prop} : @HoareState B top st (fun i x f => i = f /\ x = i) := fun s => exist _ (inleft (s, s)) _.

Program Definition put' {B : Prop} (x : st) : @HoareState B top unit (fun _ _ f => f = x) := fun  _ => exist _ (inleft (tt, x)) _.

End hoare_state_monad.

Infix ">>=" := bind (right associativity, at level 71).

Notation "x <- m ; p" := (m >>= fun x => p)
    (at level 68, right associativity,
     format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'").

(** * Errors of W *)
Inductive UnifyFailure : ty -> ty -> Prop :=
  | occ_fail  : forall v t, occurs v t -> UnifyFailure (var v) t
  | occ_fail'  : forall v t, occurs v t -> UnifyFailure t (var v)
  | diff_cons : forall n n', n <> n' -> UnifyFailure (con n) (con n')
  | con_arrow   : forall n l r, UnifyFailure (con n) (arrow l r)
  | arrow_con   : forall n l r, UnifyFailure (arrow l r) (con n)
  | arrow_left  : forall l l' r r', UnifyFailure l l' -> UnifyFailure (arrow l r) (arrow l' r')
  | arrow_right  : forall l l' r r' s, UnifyFailure (apply_subst s r) (apply_subst s r') -> UnifyFailure (arrow l r) (arrow l' r') .

Hint Constructors UnifyFailure.

Inductive SubstFailure :  Prop :=
| substFail : SubstFailure.

Hint Constructors SubstFailure.

Inductive MissingVar : id ->  Prop :=
| missingVar : forall i, MissingVar i.

Hint Constructors MissingVar.

Inductive InferFailure : Prop :=
| SubstFailure' : SubstFailure -> InferFailure
| UnifyFailure' : forall t1 t2, UnifyFailure t1 t2 -> InferFailure
| MissingVar' : forall i, MissingVar i -> InferFailure.

Hint Constructors InferFailure.

Unset Implicit Arguments.

(** * Instance of Hoare Exception-Sate Monad *)
Definition Infer := @HoareState id InferFailure.
Definition get := @get' id InferFailure.
Definition put := @put' id InferFailure.
