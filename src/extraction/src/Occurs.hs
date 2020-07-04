module Occurs where

import qualified Prelude
import qualified SimpleTypes

occurs_dec :: SimpleTypes.Coq_id -> SimpleTypes.Coq_ty -> Prelude.Bool
occurs_dec v t =
  case t of {
   SimpleTypes.Coq_var n -> SimpleTypes.eq_id_dec n v;
   SimpleTypes.Coq_con _ -> Prelude.False;
   SimpleTypes.Coq_arrow l r ->
    case occurs_dec v l of {
     Prelude.True -> Prelude.True;
     Prelude.False -> occurs_dec v r}}

