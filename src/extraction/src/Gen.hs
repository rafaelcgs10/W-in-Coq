module Gen where

import qualified Prelude
import qualified Context
import qualified Datatypes
import qualified ListIds
import qualified Schemes
import qualified SimpleTypes

gen_ty_aux :: SimpleTypes.Coq_ty -> Context.Coq_ctx -> ([]
              SimpleTypes.Coq_id) -> (,) Schemes.Coq_schm
              ([] SimpleTypes.Coq_id)
gen_ty_aux tau g l =
  case tau of {
   SimpleTypes.Coq_var i ->
    case ListIds.in_list_id i (Context.coq_FV_ctx g) of {
     Datatypes.Coq_true -> (,) (Schemes.Coq_sc_var i) l;
     Datatypes.Coq_false ->
      case ListIds.index_list_id i l of {
       Datatypes.Some j -> (,) (Schemes.Coq_sc_gen j) l;
       Datatypes.None -> (,) (Schemes.Coq_sc_gen (Datatypes.length l))
        (Datatypes.app l ((:) i []))}};
   SimpleTypes.Coq_con i -> (,) (Schemes.Coq_sc_con i) l;
   SimpleTypes.Coq_arrow tau' tau'' ->
    case gen_ty_aux tau' g l of {
     (,) sc_tau l' ->
      case gen_ty_aux tau'' g l' of {
       (,) sc_tau' l'' -> (,) (Schemes.Coq_sc_arrow sc_tau sc_tau') l''}}}

gen_ty :: SimpleTypes.Coq_ty -> Context.Coq_ctx -> Schemes.Coq_schm
gen_ty tau g =
  Datatypes.fst (gen_ty_aux tau g [])

