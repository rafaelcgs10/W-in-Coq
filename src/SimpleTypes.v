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

(** * Creates a list of type from a list of ids *)
Fixpoint ty_from_id_list (l : list id) : list ty :=
  match l with
  | nil => nil
  | x::l' => var x :: ty_from_id_list l'
  end.

Lemma length_ty_from_id_list : forall l : list id, length (ty_from_id_list l) = length l.
Proof.
  induction l; simpl; auto.
Qed.

Hint Resolve length_ty_from_id_list.
Hint Rewrite length_ty_from_id_list:RE.

