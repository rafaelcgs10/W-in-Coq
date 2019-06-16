module PeanoNat where

import qualified Prelude
import qualified Datatypes

_Nat__eq_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
_Nat__eq_dec n =
  Datatypes.nat_rec (\m -> case m of {
                            Datatypes.O -> Prelude.True;
                            Datatypes.S _ -> Prelude.False}) (\_ iHn m -> case m of {
                                                                           Datatypes.O -> Prelude.False;
                                                                           Datatypes.S m0 -> iHn m0}) n

