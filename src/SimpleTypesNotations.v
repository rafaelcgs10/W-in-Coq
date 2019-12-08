(** * Notations for Simple Types *)

Require Import SimpleTypes.

Unset Printing Notations.

Declare Custom Entry DM.
Notation "&[ e ]" := e (e custom DM at level 2).

Notation "tau -> tau'" := (arrow tau tau')
    (in custom DM at level 5, right associativity).

Notation "( e )" := e (in custom DM, e at level 2).

Notation "{ x }" := x (in custom DM, x constr).
Notation "x" := x (in custom DM at level 0, x ident).


Notation "[ e ]" := e (in custom DM, e at level 4).
Notation "a ; .. ; b" := (cons a .. (cons b nil) ..)
  (in custom DM at level 7, a custom DM at level 6, b custom DM at level 6).
Notation "i => t" := (i, t)
  (in custom DM at level 6, i constr at level 5, t constr at level 5).
Definition test := &[ [0 => 1; 2 => 3; 4 => 6] ].

Print test.

Check forall tau, &[tau -> tau] = &[(tau -> tau) -> (tau)].

Definition tt := forall tau:ty, &[ tau ] = &[ tau ].
Print tt.