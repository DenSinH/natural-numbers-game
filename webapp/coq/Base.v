Inductive mynat : Set :=
| O : mynat
| S : mynat -> mynat.

Fixpoint add (n m : mynat) : mynat :=
    match n with
    | O => m
    | S p => S (add p m)
    end.

Infix "+" := add.