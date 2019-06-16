Require Import Unify.
Require Import HoareMonad.
Require Import Infer.
Require Import SimpleTypes.
Require Import Coq.Bool.Bool.

Extraction Language Haskell.

Cd "extraction/src".

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sumorT => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

Separate Extraction runW.

