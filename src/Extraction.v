Require Import Unify.
Require Import HoareMonad.
Require Import Infer.
Require Import SimpleTypes.
Require Import Coq.Bool.Bool.

Extraction Language Haskell.

Cd "extraction/src".

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Separate Extraction runW.
