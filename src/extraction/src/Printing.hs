module Printing where

import Parser
import Data.Char
import HoareMonad
import Typing
import Datatypes
import SimpleTypes

max_ty (Coq_con _) = 0
max_ty (Coq_var n) = n
max_ty (Coq_arrow t1 t2) = max (max_ty t1) (max_ty t2)

min_ty t = min_ty' t (max_ty t)
min_ty' (Coq_con _) m = m
min_ty' (Coq_var n) m = min n m
min_ty' (Coq_arrow t1 t2) m = min (min_ty' t1 m) (min_ty' t2 m)

normalize_ty_to_O t = normalize_ty_to_O' t (min_ty t)
normalize_ty_to_O' (Coq_var n) n' = Coq_var (n - n') 
normalize_ty_to_O' (Coq_con n) _ = Coq_con n 
normalize_ty_to_O' (Coq_arrow t1 t2) n' = Coq_arrow (normalize_ty_to_O' t1 n') (normalize_ty_to_O' t2 n')

add_97_coq_var (Coq_var n) = Coq_var (n + 97)
add_97_coq_var (Coq_arrow t1 t2) = Coq_arrow (add_97_coq_var t1) (add_97_coq_var t2)
add_97_coq_var m = m

instance Show SimpleTypes.Coq_ty where
  show t = show' (add_97_coq_var (normalize_ty_to_O t)) where
             show' (Coq_var n) = coq_idToString n
             show' (Coq_con 0) = "Int"
             show' (Coq_con n) = "Const " ++ show n
             show' (Coq_arrow t1 t2) = "(" ++ (show' t1) ++ " -> " ++ (show' t2) ++ ")"

instance Show HoareMonad.UnifyFailure where
  show (Coq_occ_fail i t) = "Occurs check failure: " ++ show (Coq_var i) ++ " in " ++ show t
  show (Coq_occ_fail' i t) = "Occurs check failure: " ++ show (Coq_var i) ++ " in " ++ show t
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
