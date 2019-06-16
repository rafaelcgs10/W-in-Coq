module Datatypes where

import qualified Prelude

data Coq_unit =
   Coq_tt

data Coq_nat =
   O
 | S Coq_nat deriving Prelude.Show

nat_rect :: a1 -> (Coq_nat -> a1 -> a1) -> Coq_nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Coq_nat -> a1 -> a1) -> Coq_nat -> a1
nat_rec =
  nat_rect

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

length :: ([] a1) -> Coq_nat
length l =
  case l of {
   [] -> O;
   (:) _ l' -> S (length l')}

app :: ([] a1) -> ([] a1) -> [] a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

