module HoareMonad where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified SimpleTypes
import qualified Specif
import qualified Subst

type HoareState st b a = st -> (Prelude.Either ((,) a st) b)

ret :: a3 -> HoareState a1 a2 a3
ret x s =
  Prelude.Left ((,) x (Specif.proj1_sig s))

bind_obligation_4 :: (HoareState a1 a4 a2) -> a1 -> a4 ->
                     (Prelude.Either ((,) a3 a1) a4)
bind_obligation_4 c1 s1 r =
  Logic.eq_rect (Prelude.Right r) (Prelude.Right r)
    (Specif.proj1_sig (c1 s1))

bind :: (HoareState a1 a4 a2) -> (a2 -> HoareState a1 a4 a3) -> HoareState 
        a1 a4 a3
bind c1 c2 s1 =
  let {filtered_var = Specif.proj1_sig (c1 (Specif.proj1_sig s1))} in
  case filtered_var of {
   Prelude.Left p -> case p of {
                      (,) x s2 -> Specif.proj1_sig (c2 x s2)};
   Prelude.Right r -> bind_obligation_4 c1 s1 r}

failT :: a2 -> HoareState a1 a2 a3
failT b _ =
  Prelude.Right b

get' :: HoareState a1 a2 a1
get' s =
  Prelude.Left ((,) (Specif.proj1_sig s) (Specif.proj1_sig s))

put' :: a1 -> HoareState a1 a2 Datatypes.Coq_unit
put' x _ =
  Prelude.Left ((,) Datatypes.Coq_tt x)

data UnifyFailure =
   Coq_occ_fail SimpleTypes.Coq_id SimpleTypes.Coq_ty
 | Coq_occ_fail' SimpleTypes.Coq_id SimpleTypes.Coq_ty
 | Coq_diff_cons SimpleTypes.Coq_id SimpleTypes.Coq_id
 | Coq_con_arrow SimpleTypes.Coq_id SimpleTypes.Coq_ty SimpleTypes.Coq_ty
 | Coq_arrow_con SimpleTypes.Coq_id SimpleTypes.Coq_ty SimpleTypes.Coq_ty
 | Coq_arrow_left SimpleTypes.Coq_ty SimpleTypes.Coq_ty SimpleTypes.Coq_ty 
 SimpleTypes.Coq_ty UnifyFailure
 | Coq_arrow_right SimpleTypes.Coq_ty SimpleTypes.Coq_ty SimpleTypes.Coq_ty 
 SimpleTypes.Coq_ty Subst.Coq_substitution UnifyFailure

data SubstFailure =
   Coq_substFail

type MissingVar =
  SimpleTypes.Coq_id
  -- singleton inductive, whose constructor was missingVar
  
data InferFailure =
   SubstFailure' SubstFailure
 | UnifyFailure' SimpleTypes.Coq_ty SimpleTypes.Coq_ty UnifyFailure
 | MissingVar' SimpleTypes.Coq_id MissingVar

type Infer a = HoareState SimpleTypes.Coq_id InferFailure a

get :: HoareState SimpleTypes.Coq_id InferFailure SimpleTypes.Coq_id
get =
  get'

put :: SimpleTypes.Coq_id -> HoareState SimpleTypes.Coq_id InferFailure
       Datatypes.Coq_unit
put =
  put'

