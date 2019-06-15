Require Import Unify.
Require Import HoareMonad.
Require Import Infer.
Require Import SimpleTypes.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Local Open Scope string.
Require Import Program.


Extraction Language Haskell.

Cd "extracted".

Check (@HoareMonad.Infer (fun _ => True)).
Check (@W (Typing.var_t 0) nil).

Program Definition runInfer P a Q (C : Infer P a Q) (s0 : id) (p : P s0) : option a :=
  match C (exist _ s0 p) with
  | inleft (a', _) => Some a'
  | inright _ => None
  end.

Check runW.

Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive string => "String"  [ "[]" "(::)" ].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].


Class Show A : Type :=
  {
    show : A -> string
  }.

Instance showBool : Show bool :=
  {
    show := fun b:bool => if b then "true" else "false"
  }.

Extraction "test.hs" show.
 Check show.

Compute (show true).


Separate Extraction unify.