(** * Notations for Simple Types *)

Require Import SimpleTypes.

Declare Custom Entry DM.
Notation "&[ e ]" := e (e custom DM at level 2).

Notation "'VA'" := (var 0) (in custom DM at level 0).
Notation "tau -> tau'" := (arrow tau tau') (in custom DM at level 1, right associativity).
Notation "( e )" := e (in custom DM, e at level 2).

Notation "{ x }" := x (in custom DM, x constr).
Notation "x" := x (in custom DM at level 0, x ident).

Check forall tau, &[VA -> tau] = &[VA -> tau].
