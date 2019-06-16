module Context where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Schemes
import qualified SimpleTypes
import qualified Subst
import qualified SubstSchm

type Coq_ctx = [] ((,) SimpleTypes.Coq_id Schemes.Coq_schm)

apply_subst_ctx :: Subst.Coq_substitution -> Coq_ctx -> Coq_ctx
apply_subst_ctx s c =
  case c of {
   [] -> [];
   (:) p xs -> case p of {
                (,) x sigma -> (:) ((,) x (SubstSchm.apply_subst_schm s sigma)) (apply_subst_ctx s xs)}}

in_ctx :: SimpleTypes.Coq_id -> Coq_ctx -> Datatypes.Coq_option Schemes.Coq_schm
in_ctx y g =
  case g of {
   [] -> Datatypes.None;
   (:) p xs -> case p of {
                (,) x t -> case SimpleTypes.eq_id_dec x y of {
                            Prelude.True -> Datatypes.Some t;
                            Prelude.False -> in_ctx y xs}}}

coq_FV_ctx :: Coq_ctx -> [] SimpleTypes.Coq_id
coq_FV_ctx g =
  List.concat (List.map Schemes.coq_FV_schm (List.map Datatypes.snd g))

