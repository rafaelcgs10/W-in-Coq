Set Implicit Arguments.

Require Import Arith.Arith_base List Omega.

(** * Type Definitions *)

(** ** Identifier definition *)

(** Identifiers are just natural numbers. This eases the task of equality test *)

Definition id := nat.

(** Decidable equality of identifiers *)

Definition eq_id_dec : forall (v v' : id), {v = v'} + {v <> v'} := eq_nat_dec.

(** Type definition is direct *)

Inductive ty : Set :=
  | var : id -> ty
  | con : id -> ty
  | arrow : ty -> ty -> ty.

(** List of ids in a type *)
Fixpoint ids_ty(tau : ty) : list id :=
  match tau with
  | var i => i::nil
  | arrow l r => (ids_ty l) ++ (ids_ty r) 
  | _ => nil
  end.

(** Decidable equality test for types *)

Definition eq_ty_dec : forall (t t' : ty), {t = t'} + {t <> t'}.
  pose eq_id_dec.
  decide equality.
Defined.

