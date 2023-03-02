From NaturalNumbers Require Export Base Tutorial Addition Multiplication Power.

(* Level 0 data *)
(* name the `exact` tactic *)
(* tactics induction *)
(* Level 0 prologue *)
Example level0 (P Q : Type) (p : P) (h : P -> Q) : Q.
Proof.
    exact (h p).
Qed.
(* Level epilogue *)
(* Level end *)

Definition III := S II.
Notation "3" := III.

(* Level 1 data *)
(* name the `intro` tactic *)
(* tactics induction *)
(* Level 1 prologue *)
Example level1 : mynat -> mynat.
Proof.
    intro n.
    exact (3 * n + 2).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name the `remember` and `specialize` tactics *)
(* tactics induction *)
(* Level 2 prologue *)
Example level2 (P Q R S T U : Type)
    (p : P)
    (h : P -> Q)
    (i : Q -> R)
    (j : Q -> T)
    (k : S -> T)
    (l : T -> U)
    : U.
Proof.
    remember (h p) as q.
    remember (j q : T) as t.
    (* what does eremember do vs remember? *)
    eremember (l(t)) as u.
    exact u.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name the `apply` tactic *)
(* tactics induction *)
(* Level 3 prologue *)
Example level3 (P Q R S T U : Type)
    (p : P)
    (h : P -> Q)
    (i : Q -> R)
    (j : Q -> T)
    (k : S -> T)
    (l : T -> U)
    : U.
Proof.
    apply l.
    apply j, h.
    exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 data *)
(* name `P -> (Q -> P)` *)
(* tactics induction *)
(* Level 4 prologue *)
Example level4 (P Q : Type) : P -> (Q -> P).
Proof.
    intros p q.
    exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name `(P -> (Q -> R)) -> ((P -> Q) -> (P -> R))` *)
(* tactics induction *)
(* Level 5 prologue *)
Example level5 (P Q R : Type) : (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
    intros j f p.
    apply j.
    - exact p.
    - exact (f p).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `(P -> Q) -> ((Q -> F) -> (P -> F))` *)
(* tactics induction *)
(* Level 6 prologue *)
Example level6 (P Q F : Type) : (P -> Q) -> ((Q -> F) -> (P -> F)).
Proof.
    intros f g h.
    apply g, f.
    exact h.
Qed.
(* Level epilogue *)
(* Level end *)

Require Import Init.Datatypes.

(* todo: unimath empty type / actual empty type? *)
Definition empty := Empty_set.

(* Level 7 data *)
(* name `(P -> Q) -> ((Q -> empty) -> (P -> empty))` *)
(* tactics induction *)
(* Level 7 prologue *)
Example level7 (P Q : Type) : (P -> Q) -> ((Q -> empty) -> (P -> empty)).
Proof.
    intros f g h.
    apply g, f.
    exact h.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 8 data *)
(* name a big maze *)
(* tactics induction *)
(* Level 8 prologue *)
Example level8 (A B C D E F G H I J K L : Type)
    (f1 : A -> B) (f2 : B -> E) (f3 : E -> D) (f4 : D -> A) (f5 : E -> F)
    (f6 : F -> C) (f7 : B -> C) (f8 : F -> G) (f9 : G -> J) (f10 : I -> J)
    (f11 : J -> I) (f12 : I -> H) (f13 : E -> H) (f14 : H -> K) (f15 : I -> L)
 : A -> L.
Proof.
    intro a.
    now apply f15, f11, f9, f8, f5, f2, f1.
Qed.
(* Level epilogue *)
(* Level end *)
