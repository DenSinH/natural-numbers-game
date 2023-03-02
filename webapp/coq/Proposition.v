
(* Level 0 data *)
(* name the `exact` tactic *)
(* tactics induction *)
(* available false *)
(* Level prologue *)
Example level0 (P Q : Prop) (p : P) (h : P -> Q) : Q.
Proof.
    exact (h p).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name the `intro` tactic *)
(* tactics induction *)
(* available false *)
(* Level 1 prologue *)
Lemma imp_self (P : Prop) : P -> P.
Proof.
    intro p.
    exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name the `remember` and `specialize` tactics *)
(* tactics induction *)
(* available false *)
(* Level 2 prologue *)
Lemma maze (P Q R S T U: Prop)
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
(* available false *)
(* Level 3 prologue *)
Lemma maze2 (P Q R S T U: Prop)
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
(* available false *)
(* Level 4 prologue *)
Example level4 (P Q : Prop) : P -> (Q -> P).
Proof.
    intros p q.
    exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name `(P -> (Q -> R)) -> ((P -> Q) -> (P -> R))` *)
(* tactics induction *)
(* available false *)
(* Level 5 prologue *)
Example level5 (P Q R : Prop) : (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
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
(* available false *)
(* Level 6 prologue *)
Lemma imp_trans (P Q R : Type) : (P -> Q) -> ((Q -> R) -> (P -> R)).
Proof.
    intros f g h.
    apply g, f.
    exact h.
Qed.
(* Level epilogue *)
(* Level end *)

Lemma not_iff_impl_false (P : Prop) : ~ P <-> (P -> False).
Proof.
    unfold not.
    split.
    - trivial.
    - trivial.
Qed.

Require Setoid.

(* Level 7 data *)
(* name `(P -> Q) -> (~Q -> ~P)` *)
(* tactics induction *)
(* available false *)
(* Level 7 prologue *)
Lemma contrapositive (P Q : Prop) : (P -> Q) -> (~Q -> ~P).
Proof.
    (* requires Setoid *)
    repeat rewrite not_iff_impl_false.
    intros f g p.
    exact (g (f p)).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 8 data *)
(* name a big maze *)
(* tactics induction *)
(* available false *)
(* Level 8 prologue *)
Example level8 (A B C D E F G H I J K L : Prop)
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


