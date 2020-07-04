module Infer where

import qualified Prelude
import qualified Context
import qualified Datatypes
import qualified Gen
import qualified HoareMonad
import qualified Schemes
import qualified SimpleTypes
import qualified Specif
import qualified Subst
import qualified SubstSchm
import qualified Typing
import qualified Unify

apply_inst_subst_hoare :: SubstSchm.Coq_inst_subst -> Schemes.Coq_schm ->
                          HoareMonad.Infer SimpleTypes.Coq_ty
apply_inst_subst_hoare is_s sigma =
  let {filtered_var = SubstSchm.apply_inst_subst is_s sigma} in
  (\x ->
  case filtered_var of {
   Datatypes.Some tau -> Specif.proj1_sig (HoareMonad.ret tau x);
   Datatypes.None ->
    Specif.proj1_sig
      (HoareMonad.failT (HoareMonad.SubstFailure' HoareMonad.Coq_substFail)
        x)})

schm_inst_dep :: Schemes.Coq_schm -> HoareMonad.Infer SimpleTypes.Coq_ty
schm_inst_dep sigma =
  let {filtered_var = Schemes.max_gen_vars sigma} in
  (\x ->
  Specif.proj1_sig
    (HoareMonad.bind HoareMonad.get (\st ->
      HoareMonad.bind (HoareMonad.put ((Prelude.+) st filtered_var)) (\_ ->
        HoareMonad.bind
          (apply_inst_subst_hoare
            (SubstSchm.compute_inst_subst st filtered_var) sigma)
          HoareMonad.ret)) (Specif.proj1_sig x)))

look_dep :: SimpleTypes.Coq_id -> Context.Coq_ctx -> HoareMonad.Infer
            Schemes.Coq_schm
look_dep x g =
  let {filtered_var = Context.in_ctx x g} in
  (\x0 ->
  case filtered_var of {
   Datatypes.Some sig -> Specif.proj1_sig (HoareMonad.ret sig x0);
   Datatypes.None ->
    Specif.proj1_sig (HoareMonad.failT (HoareMonad.MissingVar' x x) x0)})

fresh :: HoareMonad.Infer SimpleTypes.Coq_id
fresh n =
  Prelude.Left ((,) (Specif.proj1_sig n) (Prelude.succ (Specif.proj1_sig n)))

addFreshCtx :: Context.Coq_ctx -> SimpleTypes.Coq_id -> SimpleTypes.Coq_id ->
               HoareMonad.Infer Context.Coq_ctx
addFreshCtx g x alpha x0 =
  Specif.proj1_sig
    (HoareMonad.ret ((:) ((,) x
      (Schemes.ty_to_schm (SimpleTypes.Coq_var alpha))) g)
      (Specif.proj1_sig x0))

coq_W :: Typing.Coq_term -> Context.Coq_ctx -> HoareMonad.Infer
         ((,) SimpleTypes.Coq_ty Subst.Coq_substitution)
coq_W e g x0 =
  case e of {
   Typing.Coq_var_t x ->
    Specif.proj1_sig
      (HoareMonad.bind (look_dep x g) (\sigma ->
        HoareMonad.bind (schm_inst_dep sigma) (\tau ->
          HoareMonad.ret ((,) tau []))) (Specif.proj1_sig x0));
   Typing.Coq_app_t l r ->
    Specif.proj1_sig
      (HoareMonad.bind (coq_W l g) (\tau1_s1 ->
        HoareMonad.bind
          (coq_W r (Context.apply_subst_ctx (Datatypes.snd tau1_s1) g))
          (\tau2_s2 ->
          HoareMonad.bind fresh (\alpha ->
            HoareMonad.bind
              (Unify.unify
                (Subst.apply_subst (Datatypes.snd tau2_s2)
                  (Datatypes.fst tau1_s1)) (SimpleTypes.Coq_arrow
                (Datatypes.fst tau2_s2) (SimpleTypes.Coq_var alpha))) (\s ->
              HoareMonad.ret ((,)
                (Subst.apply_subst s (SimpleTypes.Coq_var alpha))
                (Subst.compose_subst (Datatypes.snd tau1_s1)
                  (Subst.compose_subst (Datatypes.snd tau2_s2) s)))))))
        (Specif.proj1_sig x0));
   Typing.Coq_let_t x e1 e2 ->
    Specif.proj1_sig
      (HoareMonad.bind (coq_W e1 g) (\tau1_s1 ->
        HoareMonad.bind
          (coq_W e2 ((:) ((,) x
            (Gen.gen_ty (Datatypes.fst tau1_s1)
              (Context.apply_subst_ctx (Datatypes.snd tau1_s1) g)))
            (Context.apply_subst_ctx (Datatypes.snd tau1_s1) g)))
          (\tau2_s2 ->
          HoareMonad.ret ((,) (Datatypes.fst tau2_s2)
            (Subst.compose_subst (Datatypes.snd tau1_s1)
              (Datatypes.snd tau2_s2))))) (Specif.proj1_sig x0));
   Typing.Coq_lam_t x e' ->
    Specif.proj1_sig
      (HoareMonad.bind fresh (\alpha ->
        HoareMonad.bind (addFreshCtx g x alpha) (\g' ->
          HoareMonad.bind (coq_W e' g') (\tau_s ->
            HoareMonad.ret ((,) (SimpleTypes.Coq_arrow
              (Subst.apply_subst (Datatypes.snd tau_s) (SimpleTypes.Coq_var
                alpha)) (Datatypes.fst tau_s)) (Datatypes.snd tau_s)))))
        (Specif.proj1_sig x0));
   Typing.Coq_const_t x ->
    Specif.proj1_sig
      (HoareMonad.ret ((,) (SimpleTypes.Coq_con x) []) (Specif.proj1_sig x0))}

computeInitialState :: Context.Coq_ctx -> SimpleTypes.Coq_id
computeInitialState g =
  case g of {
   [] -> 0;
   (:) p g' ->
    case p of {
     (,) _ sigma ->
      let {filtered_var = Specif.proj1_sig (computeInitialState g')} in
      case (Prelude.<) (Schemes.max_vars_schm sigma) filtered_var of {
       Prelude.True -> filtered_var;
       Prelude.False -> Prelude.succ (Schemes.max_vars_schm sigma)}}}

runW :: Typing.Coq_term -> Context.Coq_ctx -> Prelude.Either
        ((,) SimpleTypes.Coq_ty Subst.Coq_substitution)
        HoareMonad.InferFailure
runW e g =
  let {filtered_var = Specif.proj1_sig (coq_W e g (computeInitialState g))}
  in
  case filtered_var of {
   Prelude.Left p -> case p of {
                      (,) a' _ -> Prelude.Left a'};
   Prelude.Right er -> Prelude.Right er}

