Set Implicit Arguments.

Require Import LibTactics.
Require Import SimpleTypes.


(** * Non empty list for case expressions*)

Inductive non_empty_list (A : Type) : Type :=
  | one : A -> non_empty_list A
  | cons' : A -> non_empty_list A -> non_empty_list A.

Fixpoint ty_in_non_empty_list (tau : ty) (l : non_empty_list ty) : Prop :=
  match l with
  | one tau' => if eq_ty_dec tau tau' then True else False
  | cons' tau' l' => if (eq_ty_dec tau tau') then True else ty_in_non_empty_list tau l'
end.
