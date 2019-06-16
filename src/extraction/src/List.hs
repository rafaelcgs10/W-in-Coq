module List where

import qualified Prelude
import qualified Datatypes

nth_error :: ([] a1) -> Datatypes.Coq_nat -> Datatypes.Coq_option a1
nth_error l n =
  case n of {
   Datatypes.O -> case l of {
                   [] -> Datatypes.None;
                   (:) x _ -> Datatypes.Some x};
   Datatypes.S n0 -> case l of {
                      [] -> Datatypes.None;
                      (:) _ l0 -> nth_error l0 n0}}

concat :: ([] ([] a1)) -> [] a1
concat l =
  case l of {
   [] -> [];
   (:) x l0 -> Datatypes.app x (concat l0)}

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

