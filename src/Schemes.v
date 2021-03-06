(** * The schemes
      This file contains the defintion of schemes (polymorphic types) [schm] and 
      some auxiliary definitions.
    *)

Set Implicit Arguments.

Require Import SimpleTypes.
Require Import Arith.Arith_base List Omega.
Require Import Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import LibTactics.

Require Import LibTactics.

(** * Schemes *)

Inductive schm : Type :=
| sc_var : id -> schm
| sc_con : id -> schm
| sc_gen : id -> schm
| sc_arrow : schm -> schm -> schm. 

(** * It converts a simple type into a scheme  *)

Fixpoint ty_to_schm (tau : ty) : schm :=
  match tau with
  | var n => sc_var n
  | con n => sc_con n
  | arrow t1 t2 => sc_arrow (ty_to_schm t1) (ty_to_schm t2)                 
  end.

(** * Free variables of schemes *)

Fixpoint FV_schm (sigma : schm) : list id :=
  match sigma with
  | sc_var i => i::nil
  | sc_arrow l r => (FV_schm l) ++ (FV_schm r)
  | _ => nil
  end.

Fixpoint max_gen_vars (sigma : schm) : nat :=
  match sigma with
  | sc_con _ => 0
  | sc_var _ => 0
  | sc_gen i => S i
  | sc_arrow s1 s2 => max (max_gen_vars s1) (max_gen_vars s2)
  end.

Fixpoint max_vars_schm (sigma : schm) : nat :=
  match sigma with
  | sc_con _ => 0
  | sc_var i => i
  | sc_gen _ => 0
  | sc_arrow s1 s2 => max (max_vars_schm s1) (max_vars_schm s2)
  end.

