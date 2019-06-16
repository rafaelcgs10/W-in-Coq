module Specif where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_sig a = a
  -- singleton inductive, whose constructor was exist
  
data Coq_sigT a p =
   Coq_existT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

