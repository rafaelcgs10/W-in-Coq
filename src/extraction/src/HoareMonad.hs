module HoareMonad where

import qualified Prelude
import qualified Datatypes
import qualified SimpleTypes
import qualified Specif

type HoareState st a = st -> (Prelude.Maybe ((,) a st))

ret :: a2 -> HoareState a1 a2
ret x s =
  Prelude.Just ((,) x (Specif.proj1_sig s))

bind :: (HoareState a1 a2) -> (a2 -> HoareState a1 a3) -> HoareState a1 a3
bind c1 c2 s1 =
  let {filtered_var = Specif.proj1_sig (c1 (Specif.proj1_sig s1))} in
  case filtered_var of {
   Prelude.Just p -> case p of {
                      (,) x s2 -> Specif.proj1_sig (c2 x s2)};
   Prelude.Nothing -> Prelude.Nothing}

failT :: HoareState a1 a2
failT _ =
  Prelude.Nothing

get' :: HoareState a1 a1
get' s =
  Prelude.Just ((,) (Specif.proj1_sig s) (Specif.proj1_sig s))

put' :: a1 -> HoareState a1 Datatypes.Coq_unit
put' x _ =
  Prelude.Just ((,) Datatypes.Coq_tt x)

type Infer a = HoareState SimpleTypes.Coq_id a

get :: HoareState SimpleTypes.Coq_id SimpleTypes.Coq_id
get =
  get'

put :: SimpleTypes.Coq_id -> HoareState SimpleTypes.Coq_id Datatypes.Coq_unit
put =
  put'

