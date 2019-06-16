module Printing where

import Parser
import Data.Char
import HoareMonad
import Typing
import Datatypes
import SimpleTypes

instance Show Datatypes.Coq_nat where
  show n = coq_idToString n 

instance Eq Datatypes.Coq_nat where
  O == O = True
  (S n) == (S n') = n == n
  
instance Ord Datatypes.Coq_nat where
  O `compare` O = EQ
  O `compare` S O = LT
  S O `compare` O = GT
  (S n) `compare` (S m) = n `compare` m
  O < O = False
  O < (S O) = True
  (S n) < (S m) = n < m
  max n m = if n < m then m else n
  min n m = if n < m then n else m

max_ty (Coq_con _) = O
max_ty (Coq_var n) = n
max_ty (Coq_arrow t1 t2) = max (max_ty t1) (max_ty t2)
  
min_ty (Coq_con _) = O
min_ty (Coq_var n) = n
min_ty (Coq_arrow t1 t2) = min (min_ty t1) (min_ty t2)

minus_id O m = O
minus_id m O = m
minus_id (S m) (S n) = minus_id m n

normalize_ty_to_O t = normalize_ty_to_O' t (min_ty t)
normalize_ty_to_O' (Coq_var n) n' = Coq_var (minus_id n n') 
normalize_ty_to_O' (Coq_con n) _ = Coq_con n 
normalize_ty_to_O' (Coq_arrow t1 t2) n' = Coq_arrow (normalize_ty_to_O' t1 n') (normalize_ty_to_O' t2 n')

add_97_to_id n = add_97_to_id' n 97
add_97_to_id' n 0 = n
add_97_to_id' n m = add_97_to_id' (S n) (m - 1)

instance Show SimpleTypes.Coq_ty where
  show t = show' (normalize_ty_to_O t) where
             show' (Coq_var n) = show (add_97_to_id n)
             show' (Coq_con O) = "Int"
             show' (Coq_con n) = "Const " ++ show n
             show' (Coq_arrow t1 t2) = (show' t1) ++ " -> " ++ (show' t2)

instance Show HoareMonad.UnifyFailure where
  show (Coq_occ_fail i t) = "Occurs check failure: " ++ show i ++ " in " ++ show t
  show (Coq_occ_fail' i t) = "Occurs check failure: " ++ show i ++ " in " ++ show t
  show (Coq_diff_cons i j) = "Can't unify " ++ show (Coq_con i) ++ " and " ++ show (Coq_con j)
  show (Coq_con_arrow i t1 t2) = "Can't unify " ++ show (Coq_con i) ++ " and " ++ show (Coq_arrow t1 t2)
  show (Coq_arrow_con i t1 t2) = "Can't unify " ++ show (Coq_con i) ++ " and " ++ show (Coq_arrow t1 t2)
  show (Coq_arrow_left _ _ _ _ e) = show e
  show (Coq_arrow_right _ _ _ _ _ e) = show e

instance Show HoareMonad.SubstFailure where
  show _ = "Substitution failed"

instance Show HoareMonad.InferFailure where
  show (SubstFailure' er) = show er
  show (UnifyFailure' _ _ er) = show er
  show (MissingVar' _ er) = "var " ++ show er ++ " not in scope"
