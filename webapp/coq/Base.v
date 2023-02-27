Inductive mynat : Set :=
| O : mynat
| S : mynat -> mynat.

Fixpoint add (n m : mynat) : mynat :=
    match m with
    | O => n
    | S p => S (add n p)
    end.

Infix "+" := add.
Notation "(+)" := add (only parsing).
Notation "( f +)" := (add f) (only parsing).
Notation "(+ f )" := (fun g => add g f) (only parsing).

Notation "0" := O.