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

type Coq_constraints =
  Specif.Coq_sigT Varctxt.Coq_varctxt
  ((,) SimpleTypes.Coq_ty SimpleTypes.Coq_ty)

get_ctxt :: Coq_constraints -> Varctxt.Coq_varctxt
get_ctxt c =
  case c of {
   Specif.Coq_existT v _ -> v}

get_tys :: Coq_constraints -> (,) SimpleTypes.Coq_ty SimpleTypes.Coq_ty
get_tys c =
  case c of {
   Specif.Coq_existT _ l -> l}

mk_constraints :: Varctxt.Coq_varctxt -> SimpleTypes.Coq_ty ->
                  SimpleTypes.Coq_ty -> Coq_constraints
mk_constraints c t1 t2 =
  Specif.Coq_existT c ((,) t1 t2)

type Coq_unify_type =
  () -> Prelude.Either Subst.Coq_substitution HoareMonad.UnifyFailure

unify'_obligation_1 :: SimpleTypes.Coq_id -> SimpleTypes.Coq_ty ->
                       HoareMonad.UnifyFailure
unify'_obligation_1 i t =
  HoareMonad.Coq_occ_fail i t

unify'_obligation_4 :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_id ->
                       HoareMonad.UnifyFailure
unify'_obligation_4 t i =
  HoareMonad.Coq_occ_fail' i t

unify'_obligation_8 :: SimpleTypes.Coq_id -> SimpleTypes.Coq_id ->
                       HoareMonad.UnifyFailure
unify'_obligation_8 i j =
  HoareMonad.Coq_diff_cons i j

unify'_obligation_11 :: Coq_constraints -> SimpleTypes.Coq_ty ->
                        SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty ->
                        SimpleTypes.Coq_ty -> HoareMonad.UnifyFailure ->
                        HoareMonad.UnifyFailure
unify'_obligation_11 _ l1 r1 l2 r2 e =
  HoareMonad.Coq_arrow_left l1 l2 r1 r2 e

unify'_obligation_14 :: Coq_constraints -> (Coq_constraints -> () ->
                        Coq_unify_type) -> SimpleTypes.Coq_ty ->
                        SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty ->
                        SimpleTypes.Coq_ty -> Subst.Coq_substitution ->
                        HoareMonad.UnifyFailure -> HoareMonad.UnifyFailure
unify'_obligation_14 _ _ l1 r1 l2 r2 s1 e =
  HoareMonad.Coq_arrow_right l1 l2 r1 r2 s1 e

unify'_obligation_16 :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty ->
                        SimpleTypes.Coq_id -> HoareMonad.UnifyFailure
unify'_obligation_16 wildcard' wildcard'0 wildcard'1 =
  HoareMonad.Coq_arrow_con wildcard'1 wildcard' wildcard'0

unify'_obligation_17 :: SimpleTypes.Coq_id -> SimpleTypes.Coq_ty ->
                        SimpleTypes.Coq_ty -> HoareMonad.UnifyFailure
unify'_obligation_17 wildcard' wildcard'0 wildcard'1 =
  HoareMonad.Coq_con_arrow wildcard' wildcard'0 wildcard'1

unify' :: Coq_constraints -> Prelude.Either Subst.Coq_substitution
          HoareMonad.UnifyFailure
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
          Prelude.True -> Prelude.Right (unify'_obligation_1 i t0);
          Prelude.False ->
           case SimpleTypes.eq_ty_dec (SimpleTypes.Coq_var i) t0 of {
            Prelude.True -> Prelude.Left [];
            Prelude.False -> Prelude.Left ((:) ((,) i t0) [])}};
        SimpleTypes.Coq_con wildcard' ->
         case t0 of {
          SimpleTypes.Coq_var i ->
           let {t1 = SimpleTypes.Coq_con wildcard'} in
           let {filtered_var0 = Occurs.occurs_dec i t1} in
           case filtered_var0 of {
            Prelude.True -> Prelude.Right (unify'_obligation_4 t1 i);
            Prelude.False ->
             case SimpleTypes.eq_ty_dec (SimpleTypes.Coq_var i) t1 of {
              Prelude.True -> Prelude.Left [];
              Prelude.False -> Prelude.Left ((:) ((,) i t1) [])}};
          SimpleTypes.Coq_con j ->
           case SimpleTypes.eq_id_dec wildcard' j of {
            Prelude.True -> Prelude.Left [];
            Prelude.False -> Prelude.Right (unify'_obligation_8 wildcard' j)};
          SimpleTypes.Coq_arrow wildcard'0 wildcard'1 -> Prelude.Right
           (unify'_obligation_17 wildcard' wildcard'0 wildcard'1)};
        SimpleTypes.Coq_arrow wildcard' wildcard'0 ->
         case t0 of {
          SimpleTypes.Coq_var i ->
           let {t1 = SimpleTypes.Coq_arrow wildcard' wildcard'0} in
           let {filtered_var0 = Occurs.occurs_dec i t1} in
           case filtered_var0 of {
            Prelude.True -> Prelude.Right (unify'_obligation_4 t1 i);
            Prelude.False ->
             case SimpleTypes.eq_ty_dec (SimpleTypes.Coq_var i) t1 of {
              Prelude.True -> Prelude.Left [];
              Prelude.False -> Prelude.Left ((:) ((,) i t1) [])}};
          SimpleTypes.Coq_con wildcard'1 -> Prelude.Right
           (unify'_obligation_16 wildcard' wildcard'0 wildcard'1);
          SimpleTypes.Coq_arrow l2 r2 ->
           let {
            filtered_var0 = unify'0
                              (mk_constraints (get_ctxt x) wildcard' l2) __}
           in
           case filtered_var0 of {
            Prelude.Left s ->
             let {
              filtered_var1 = unify'0
                                (mk_constraints
                                  (Varctxt.minus (get_ctxt x) (Subst.dom s))
                                  (Subst.apply_subst s wildcard'0)
                                  (Subst.apply_subst s r2)) __}
             in
             case filtered_var1 of {
              Prelude.Left s0 -> Prelude.Left (Subst.compose_subst s s0);
              Prelude.Right e -> Prelude.Right
               (unify'_obligation_14 x (\l0 _ -> unify'0 l0) wildcard'
                 wildcard'0 l2 r2 s e)};
            Prelude.Right e -> Prelude.Right
             (unify'_obligation_11 x wildcard' wildcard'0 l2 r2 e)}}}})}
  in fix_F_sub l __

ids_ty_dep :: SimpleTypes.Coq_ty -> ([] SimpleTypes.Coq_id)
ids_ty_dep tau =
  case tau of {
   SimpleTypes.Coq_var i -> (:) i [];
   SimpleTypes.Coq_con _ -> [];
   SimpleTypes.Coq_arrow l r -> Datatypes.app (ids_ty_dep l) (ids_ty_dep r)}

ids_ty_dep2 :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty ->
               ([] SimpleTypes.Coq_id)
ids_ty_dep2 tau tau' =
  case tau of {
   SimpleTypes.Coq_var i ->
    case tau' of {
     SimpleTypes.Coq_var j -> (:) i ((:) j []);
     SimpleTypes.Coq_con _ -> (:) i [];
     SimpleTypes.Coq_arrow l r -> (:) i
      (Datatypes.app (ids_ty_dep l) (ids_ty_dep r))};
   SimpleTypes.Coq_con _ ->
    case tau' of {
     SimpleTypes.Coq_var j -> (:) j [];
     SimpleTypes.Coq_con _ -> [];
     SimpleTypes.Coq_arrow l r -> Datatypes.app (ids_ty_dep l) (ids_ty_dep r)};
   SimpleTypes.Coq_arrow l r ->
    case tau' of {
     SimpleTypes.Coq_var j -> (:) j
      (Datatypes.app (ids_ty_dep l) (ids_ty_dep r));
     SimpleTypes.Coq_con _ -> Datatypes.app (ids_ty_dep l) (ids_ty_dep r);
     SimpleTypes.Coq_arrow l' r' ->
      Datatypes.app (ids_ty_dep2 l l') (ids_ty_dep2 r r')}}

unify'' :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty -> Specif.Coq_sigT
           Varctxt.Coq_varctxt
           (Prelude.Either Subst.Coq_substitution HoareMonad.UnifyFailure)
unify'' t1 t2 =
  let {dep = ids_ty_dep2 t1 t2} in
  Specif.Coq_existT dep (unify' (mk_constraints dep t1 t2))

unify :: SimpleTypes.Coq_ty -> SimpleTypes.Coq_ty -> HoareMonad.Infer
         Subst.Coq_substitution
unify tau1 tau2 =
  let {filtered_var = unify'' tau1 tau2} in
  (\x ->
  case filtered_var of {
   Specif.Coq_existT _ s ->
    case s of {
     Prelude.Left s0 -> Specif.proj1_sig (HoareMonad.ret s0 x);
     Prelude.Right error ->
      Specif.proj1_sig
        (HoareMonad.failT (HoareMonad.UnifyFailure' tau1 tau2 error) x)}})

