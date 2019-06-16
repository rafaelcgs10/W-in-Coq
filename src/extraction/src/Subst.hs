module Subst where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified SimpleTypes

type Coq_substitution = [] ((,) SimpleTypes.Coq_id SimpleTypes.Coq_ty)

find_subst :: ([] ((,) SimpleTypes.Coq_id SimpleTypes.Coq_ty)) -> SimpleTypes.Coq_id -> Datatypes.Coq_option SimpleTypes.Coq_ty
find_subst s i =
  case s of {
   [] -> Datatypes.None;
   (:) p s' -> case p of {
                (,) v t' -> case SimpleTypes.eq_id_dec v i of {
                             Prelude.True -> Datatypes.Some t';
                             Prelude.False -> find_subst s' i}}}

apply_subst :: Coq_substitution -> SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty
apply_subst s t =
  case t of {
   SimpleTypes.Coq_var i -> case find_subst s i of {
                             Datatypes.Some t' -> t';
                             Datatypes.None -> SimpleTypes.Coq_var i};
   SimpleTypes.Coq_con i -> SimpleTypes.Coq_con i;
   SimpleTypes.Coq_arrow l r -> SimpleTypes.Coq_arrow (apply_subst s l) (apply_subst s r)}

dom :: Coq_substitution -> [] SimpleTypes.Coq_id
dom s =
  List.map Datatypes.fst s

apply_subst_list :: Coq_substitution -> Coq_substitution -> Coq_substitution
apply_subst_list s1 s2 =
  case s1 of {
   [] -> [];
   (:) p s1' -> case p of {
                 (,) i t -> (:) ((,) i (apply_subst s2 t)) (apply_subst_list s1' s2)}}

compose_subst :: Coq_substitution -> Coq_substitution -> [] ((,) SimpleTypes.Coq_id SimpleTypes.Coq_ty)
compose_subst s1 s2 =
  Datatypes.app (apply_subst_list s1 s2) s2

