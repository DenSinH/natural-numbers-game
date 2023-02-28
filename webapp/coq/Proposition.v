(* Level 0 *)
Example level0 (P Q : Prop) (p : P) (h : P -> Q) : Q.
Proof.
    exact (h p).
Qed.

(* Level 1 *)
Lemma imp_self (P : Prop) : P -> P.
Proof.
    intro p.
    exact p.
Qed.

(* Level 2 *)
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

(* Level 3 *)
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

(* Level 4 *)
Example level4 (P Q : Prop) : P -> (Q -> P).
Proof.
    intros p q.
    exact p.
Qed.

(* Level 5 *)
Example level5 (P Q R : Prop) : (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
    intros j f p.
    apply j.
    - exact p.
    - exact (f p).
Qed.

(* Level 6 *)
Lemma imp_trans (P Q R : Type) : (P -> Q) -> ((Q -> R) -> (P -> R)).
Proof.
    intros f g h.
    apply g, f.
    exact h.
Qed.

Lemma not_iff_impl_false (P : Prop) : ~ P <-> (P -> False).
Proof.
    unfold not.
    split.
    - trivial.
    - trivial.
Qed.

Require Setoid.

(* Level 7 *)
Lemma contrapositive (P Q : Prop) : (P -> Q) -> (~Q -> ~P).
Proof.
    (* requires Setoid *)
    repeat rewrite not_iff_impl_false.
    intros f g p.
    exact (g (f p)).
Qed.

(* Level 8 *)
Example level8 (A B C D E F G H I J K L : Prop)
(f1 : A -> B) (f2 : B -> E) (f3 : E -> D) (f4 : D -> A) (f5 : E -> F)
(f6 : F -> C) (f7 : B -> C) (f8 : F -> G) (f9 : G -> J) (f10 : I -> J)
(f11 : J -> I) (f12 : I -> H) (f13 : E -> H) (f14 : H -> K) (f15 : I -> L)
 : A -> L.
Proof.
    intro a.
    now apply f15, f11, f9, f8, f5, f2, f1.
Qed.


