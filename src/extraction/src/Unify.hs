module Unify where

import qualified Prelude
import qualified Datatypes
import qualified HoareMonad
import qualified Occurs
import qualified SimpleTypes
import qualified Specif
import qualified Subst
import qualified Varctxt

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_constraints = Specif.Coq_sigT Varctxt.Coq_varctxt ((,) SimpleTypes.Coq_ty SimpleTypes.Coq_ty)

get_ctxt :: Coq_constraints -> Varctxt.Coq_varctxt
get_ctxt c =
  case c of {
   Specif.Coq_existT v _ -> v}

get_tys :: Coq_constraints -> (,) SimpleTypes.Coq_ty SimpleTypes.Coq_ty
get_tys c =
  case c of {
   Specif.Coq_existT _ l -> l}

mk_constraints :: Varctxt.Coq_varctxt -> SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty -> Coq_constraints
mk_constraints c t1 t2 =
  Specif.Coq_existT c ((,) t1 t2)

unify' :: Coq_constraints -> Prelude.Maybe Subst.Coq_substitution
unify' l =
  let {
   fix_F_sub x =
     let {unify'0 = \l0 -> fix_F_sub (Specif.proj1_sig l0)} in
     (\_ ->
     let {filtered_var = get_tys x} in
     case filtered_var of {
      (,) t t0 ->
       case t of {
        SimpleTypes.Coq_var i ->
         let {filtered_var0 = Occurs.occurs_dec i t0} in
         case filtered_var0 of {
          Prelude.True -> Prelude.Nothing;
          Prelude.False -> case SimpleTypes.eq_ty_dec (SimpleTypes.Coq_var i) t0 of {
                            Prelude.True -> Prelude.Just [];
                            Prelude.False -> Prelude.Just ((:) ((,) i t0) [])}};
        SimpleTypes.Coq_con wildcard' ->
         case t0 of {
          SimpleTypes.Coq_var i ->
           let {t1 = SimpleTypes.Coq_con wildcard'} in
           let {filtered_var0 = Occurs.occurs_dec i t1} in
           case filtered_var0 of {
            Prelude.True -> Prelude.Nothing;
            Prelude.False -> case SimpleTypes.eq_ty_dec (SimpleTypes.Coq_var i) t1 of {
                              Prelude.True -> Prelude.Just [];
                              Prelude.False -> Prelude.Just ((:) ((,) i t1) [])}};
          SimpleTypes.Coq_con j -> case SimpleTypes.eq_id_dec wildcard' j of {
                                    Prelude.True -> Prelude.Just [];
                                    Prelude.False -> Prelude.Nothing};
          SimpleTypes.Coq_arrow _ _ -> Prelude.Nothing};
        SimpleTypes.Coq_arrow wildcard' wildcard'0 ->
         case t0 of {
          SimpleTypes.Coq_var i ->
           let {t1 = SimpleTypes.Coq_arrow wildcard' wildcard'0} in
           let {filtered_var0 = Occurs.occurs_dec i t1} in
           case filtered_var0 of {
            Prelude.True -> Prelude.Nothing;
            Prelude.False -> case SimpleTypes.eq_ty_dec (SimpleTypes.Coq_var i) t1 of {
                              Prelude.True -> Prelude.Just [];
                              Prelude.False -> Prelude.Just ((:) ((,) i t1) [])}};
          SimpleTypes.Coq_con _ -> Prelude.Nothing;
          SimpleTypes.Coq_arrow l2 r2 ->
           let {filtered_var0 = unify'0 (mk_constraints (get_ctxt x) wildcard' l2) __} in
           case filtered_var0 of {
            Prelude.Just s ->
             let {filtered_var1 = unify'0 (mk_constraints (Varctxt.minus (get_ctxt x) (Subst.dom s)) (Subst.apply_subst s wildcard'0) (Subst.apply_subst s r2)) __} in
             case filtered_var1 of {
              Prelude.Just s0 -> Prelude.Just (Subst.compose_subst s s0);
              Prelude.Nothing -> Prelude.Nothing};
            Prelude.Nothing -> Prelude.Nothing}}}})}
  in fix_F_sub l __

ids_ty_dep :: SimpleTypes.Coq_ty -> ([] SimpleTypes.Coq_id)
ids_ty_dep tau =
  case tau of {
   SimpleTypes.Coq_var i -> (:) i [];
   SimpleTypes.Coq_con _ -> [];
   SimpleTypes.Coq_arrow l r -> Datatypes.app (ids_ty_dep l) (ids_ty_dep r)}

ids_ty_dep2 :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty -> ([] SimpleTypes.Coq_id)
ids_ty_dep2 tau tau' =
  case tau of {
   SimpleTypes.Coq_var i ->
    case tau' of {
     SimpleTypes.Coq_var j -> (:) i ((:) j []);
     SimpleTypes.Coq_con _ -> (:) i [];
     SimpleTypes.Coq_arrow l r -> (:) i (Datatypes.app (ids_ty_dep l) (ids_ty_dep r))};
   SimpleTypes.Coq_con _ ->
    case tau' of {
     SimpleTypes.Coq_var j -> (:) j [];
     SimpleTypes.Coq_con _ -> [];
     SimpleTypes.Coq_arrow l r -> Datatypes.app (ids_ty_dep l) (ids_ty_dep r)};
   SimpleTypes.Coq_arrow l r ->
    case tau' of {
     SimpleTypes.Coq_var j -> (:) j (Datatypes.app (ids_ty_dep l) (ids_ty_dep r));
     SimpleTypes.Coq_con _ -> Datatypes.app (ids_ty_dep l) (ids_ty_dep r);
     SimpleTypes.Coq_arrow l' r' -> Datatypes.app (ids_ty_dep2 l l') (ids_ty_dep2 r r')}}

unify'' :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty -> Specif.Coq_sigT Varctxt.Coq_varctxt (Prelude.Maybe Subst.Coq_substitution)
unify'' t1 t2 =
  let {dep = ids_ty_dep2 t1 t2} in Specif.Coq_existT dep (unify' (mk_constraints dep t1 t2))

unify :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty -> HoareMonad.Infer Subst.Coq_substitution
unify tau1 tau2 =
  let {filtered_var = unify'' tau1 tau2} in
  (\x ->
  case filtered_var of {
   Specif.Coq_existT _ s -> case s of {
                             Prelude.Just s0 -> Specif.proj1_sig (HoareMonad.ret s0 x);
                             Prelude.Nothing -> Specif.proj1_sig (HoareMonad.failT x)}})

