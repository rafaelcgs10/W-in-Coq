Set Implicit Arguments.

Definition projTS {P} (rs : {n1 : nat & {n2 : nat | P n1 n2}}) : (nat * nat) :=
  match rs with
  | existT _ n1 (exist _ n2 _) => (n1 ,n2)
  end.

Check projTS.

Definition someNats : {n1 : nat & {n2 : nat | n1 > n2}}. 
  refine (existT _ 2 (exist _ 1 _)).
  auto.
Defined.
Unset Printing Notations.

Check projTS someNats.
