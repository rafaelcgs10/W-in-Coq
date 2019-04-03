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

(** * Substitutions for Schemes *)

Fixpoint ty_to_schm (tau : ty) : schm :=
match tau with
  | var n => sc_var n
  | con n => sc_con n
  | arrow t1 t2 => sc_arrow (ty_to_schm t1) (ty_to_schm t2)                 
end.

(** * Substitution to make a Scheme a simple Type *)

Definition inst_subst := list ty.

Definition ids_inst_subst (s : inst_subst) : list id := List.concat (List.map ids_ty s).

Inductive schm_check : Type :=
  | Some_schm : ty -> schm_check
  | Error_schm : schm_check.

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

