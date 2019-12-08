(** * Notations for Simple Types *)

Require Import SimpleTypes.

Unset Printing Notations.

Declare Custom Entry DM.
Notation "&[ e ]" := e (e custom DM at level 2).

Notation "tau -> tau'" := (arrow tau tau')
    (in custom DM at level 2, right associativity).

Notation "( e )" := e (in custom DM, e at level 2).

Notation "{ x }" := x (in custom DM, x constr).
Notation "x" := x (in custom DM at level 0, x ident).

Check forall tau, &[tau -> tau] = &[((tau -> tau) -> (tau))].
