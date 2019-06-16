module SubstSchm where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Schemes
import qualified SimpleTypes
import qualified Subst

apply_subst_schm :: Subst.Coq_substitution -> Schemes.Coq_schm -> Schemes.Coq_schm
apply_subst_schm s sigma =
  case sigma of {
   Schemes.Coq_sc_var i -> Schemes.ty_to_schm (Subst.apply_subst s (SimpleTypes.Coq_var i));
   Schemes.Coq_sc_arrow l r -> Schemes.Coq_sc_arrow (apply_subst_schm s l) (apply_subst_schm s r);
   x -> x}

type Coq_inst_subst = [] SimpleTypes.Coq_ty

apply_inst_subst :: Coq_inst_subst -> Schemes.Coq_schm -> Datatypes.Coq_option SimpleTypes.Coq_ty
apply_inst_subst is_s sigma =
  case sigma of {
   Schemes.Coq_sc_var v -> Datatypes.Some (SimpleTypes.Coq_var v);
   Schemes.Coq_sc_con c -> Datatypes.Some (SimpleTypes.Coq_con c);
   Schemes.Coq_sc_gen x -> List.nth_error is_s x;
   Schemes.Coq_sc_arrow ts1 ts2 ->
    case apply_inst_subst is_s ts1 of {
     Datatypes.Some t1 -> case apply_inst_subst is_s ts2 of {
                           Datatypes.Some t2 -> Datatypes.Some (SimpleTypes.Coq_arrow t1 t2);
                           Datatypes.None -> Datatypes.None};
     Datatypes.None -> Datatypes.None}}

compute_inst_subst :: SimpleTypes.Coq_id -> Datatypes.Coq_nat -> [] SimpleTypes.Coq_ty
compute_inst_subst st n =
  case n of {
   Datatypes.O -> [];
   Datatypes.S n' -> (:) (SimpleTypes.Coq_var st) (compute_inst_subst (Datatypes.S st) n')}

