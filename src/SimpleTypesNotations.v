(** * Notations for Simple Types *)
(*  This notation is in a separated file to avoid conflict with the Ltac in MyLtacs file *)

Require Import SimpleTypes.

Declare Custom Entry DM.
Notation "&[ e ]" := e (e custom DM at level 2).

Notation "tau -> tau'" := (arrow tau tau')
    (in custom DM at level 2, right associativity).

Notation "( e )" := e (in custom DM, e at level 2).

Notation "{ x }" := x (in custom DM, x constr).
Notation "x" := x (in custom DM at level 0, x ident).
