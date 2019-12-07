(** * Notations for Simple Types *)

Set Implicit Arguments.

Require Import SimpleTypes.

Declare Custom Entry DM.
Notation "[ e ]" := e (e custom DM at level 2).

Notation "'a'" := (var 0) (in custom DM at level 0).
Notation "i" := (var i) (in custom DM at level 0, i ident).
Notation "tau -> tau'" := (arrow tau tau') (in custom DM at level 1, left associativity).
Notation "( e )" := e (in custom DM, e at level 2).

Notation "x" := x (in custom DM at level 0, x ident).

Check forall tau, [a -> tau] = [a -> tau].
