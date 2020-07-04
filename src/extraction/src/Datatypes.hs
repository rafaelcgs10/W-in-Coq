module Datatypes where

import qualified Prelude

data Coq_unit =
   Coq_tt

data Coq_bool =
   Coq_true
 | Coq_false

data Coq_option a =
   Some a
 | None

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

length :: ([] a1) -> Prelude.Int
length l =
  case l of {
   [] -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: ([] a1) -> ([] a1) -> [] a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

