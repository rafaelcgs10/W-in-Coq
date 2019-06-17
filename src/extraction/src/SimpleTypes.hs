module SimpleTypes where

import qualified Prelude
import qualified Specif

type Coq_id = Prelude.Int

eq_id_dec :: Coq_id -> Coq_id -> Prelude.Bool
eq_id_dec =
  (Prelude.==)

data Coq_ty =
   Coq_var Coq_id
 | Coq_con Coq_id
 | Coq_arrow Coq_ty Coq_ty

ty_rect :: (Coq_id -> a1) -> (Coq_id -> a1) -> (Coq_ty -> a1 -> Coq_ty -> a1 -> a1) -> Coq_ty -> a1
ty_rect f f0 f1 t =
  case t of {
   Coq_var i -> f i;
   Coq_con i -> f0 i;
   Coq_arrow t0 t1 -> f1 t0 (ty_rect f f0 f1 t0) t1 (ty_rect f f0 f1 t1)}

ty_rec :: (Coq_id -> a1) -> (Coq_id -> a1) -> (Coq_ty -> a1 -> Coq_ty -> a1 -> a1) -> Coq_ty -> a1
ty_rec =
  ty_rect

eq_ty_dec :: Coq_ty -> Coq_ty -> Prelude.Bool
eq_ty_dec t t' =
  ty_rec (\i x -> case x of {
                   Coq_var i0 -> Specif.sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (eq_id_dec i i0);
                   _ -> Prelude.False}) (\i x ->
    case x of {
     Coq_con i0 -> Specif.sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (eq_id_dec i i0);
     _ -> Prelude.False}) (\_ h _ h0 x ->
    case x of {
     Coq_arrow t2 t3 -> Specif.sumbool_rec (\_ -> Specif.sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h0 t3)) (\_ -> Prelude.False) (h t2);
     _ -> Prelude.False}) t t'

