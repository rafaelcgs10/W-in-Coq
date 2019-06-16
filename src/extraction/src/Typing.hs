module Typing where

import qualified Prelude
import qualified SimpleTypes

data Coq_term =
   Coq_var_t SimpleTypes.Coq_id
 | Coq_app_t Coq_term Coq_term
 | Coq_let_t SimpleTypes.Coq_id Coq_term Coq_term
 | Coq_lam_t SimpleTypes.Coq_id Coq_term
 | Coq_const_t SimpleTypes.Coq_id
 deriving Prelude.Show

