module Schemes where

import qualified Prelude
import qualified Datatypes
import qualified SimpleTypes

data Coq_schm =
   Coq_sc_var SimpleTypes.Coq_id
 | Coq_sc_con SimpleTypes.Coq_id
 | Coq_sc_gen SimpleTypes.Coq_id
 | Coq_sc_arrow Coq_schm Coq_schm

ty_to_schm :: SimpleTypes.Coq_ty -> Coq_schm
ty_to_schm tau =
  case tau of {
   SimpleTypes.Coq_var n -> Coq_sc_var n;
   SimpleTypes.Coq_con n -> Coq_sc_con n;
   SimpleTypes.Coq_arrow t1 t2 -> Coq_sc_arrow (ty_to_schm t1) (ty_to_schm t2)}

coq_FV_schm :: Coq_schm -> [] SimpleTypes.Coq_id
coq_FV_schm sigma =
  case sigma of {
   Coq_sc_var i -> (:) i [];
   Coq_sc_arrow l r -> Datatypes.app (coq_FV_schm l) (coq_FV_schm r);
   _ -> []}

max_gen_vars :: Coq_schm -> Prelude.Int
max_gen_vars sigma =
  case sigma of {
   Coq_sc_gen i -> Prelude.succ i;
   Coq_sc_arrow s1 s2 -> Prelude.max (max_gen_vars s1) (max_gen_vars s2);
   _ -> 0}

max_vars_schm :: Coq_schm -> Prelude.Int
max_vars_schm sigma =
  case sigma of {
   Coq_sc_var i -> i;
   Coq_sc_arrow s1 s2 -> Prelude.max (max_vars_schm s1) (max_vars_schm s2);
   _ -> 0}

