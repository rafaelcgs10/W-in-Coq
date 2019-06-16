module Varctxt where

import qualified Prelude
import qualified SimpleTypes

type Coq_varctxt = [] SimpleTypes.Coq_id

remove :: SimpleTypes.Coq_id -> Coq_varctxt -> Coq_varctxt
remove v ctx =
  case ctx of {
   [] -> [];
   (:) y ys -> case SimpleTypes.eq_id_dec y v of {
                Prelude.True -> remove v ys;
                Prelude.False -> (:) y (remove v ys)}}

minus :: Coq_varctxt -> ([] SimpleTypes.Coq_id) -> Coq_varctxt
minus c xs =
  case xs of {
   [] -> c;
   (:) x xs0 -> remove x (minus c xs0)}

