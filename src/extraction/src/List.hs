module List where

import qualified Prelude
import qualified Datatypes

nth_error :: ([] a1) -> Prelude.Int -> Datatypes.Coq_option a1
nth_error l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> case l of {
            [] -> Datatypes.None;
            (:) x _ -> Datatypes.Some x})
    (\n0 -> case l of {
             [] -> Datatypes.None;
             (:) _ l0 -> nth_error l0 n0})
    n

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

