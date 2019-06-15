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

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive string => "String"  [ "[]" "(::)" ].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Class Show A : Type :=
  {
    show : A -> string
  }.

Separate Extraction runW.

Instance showBool : Show bool :=
  {
    show := fun b:bool => if b then "true" else "false"
  }.

Extraction "test.hs" show.
 Check show.

Compute (show true).

