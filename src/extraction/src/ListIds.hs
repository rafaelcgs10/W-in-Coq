module ListIds where

import qualified Prelude
import qualified Datatypes
import qualified SimpleTypes

in_list_id :: SimpleTypes.Coq_id -> ([] SimpleTypes.Coq_id) ->
              Datatypes.Coq_bool
in_list_id i l =
  case l of {
   [] -> Datatypes.Coq_false;
   (:) x l' ->
    case SimpleTypes.eq_id_dec x i of {
     Prelude.True -> Datatypes.Coq_true;
     Prelude.False -> in_list_id i l'}}

index_list_id_aux :: SimpleTypes.Coq_id -> SimpleTypes.Coq_id -> ([]
                     SimpleTypes.Coq_id) -> Datatypes.Coq_option
                     SimpleTypes.Coq_id
index_list_id_aux count i l =
  case l of {
   [] -> Datatypes.None;
   (:) x l' ->
    case SimpleTypes.eq_id_dec x i of {
     Prelude.True -> Datatypes.Some count;
     Prelude.False -> index_list_id_aux (Prelude.succ count) i l'}}

index_list_id :: SimpleTypes.Coq_id -> ([] SimpleTypes.Coq_id) ->
                 Datatypes.Coq_option SimpleTypes.Coq_id
index_list_id i l =
  index_list_id_aux 0 i l

