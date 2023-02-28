From NaturalNumbers Require Import Base Tutorial Addition Multiplication Power.


Fact succ_inj {a b : mynat} : S a = S b -> a = b.
Proof.
    intro h.
    inversion h.
    reflexivity.
Qed.

Fact zero_ne_succ (a : mynat) : 0 <> S a.
Proof.
    discriminate.
Qed.

(* Level 0 *)
Lemma succ_inj' {a b : mynat} (hs : S a = S b) : a = b.
Proof.
    exact (succ_inj hs).
    (* apply succ_inj.
       exact hs. *)
    (* inversion hs.
       reflexivity. *)
Qed.

(* Level 1 *)
Lemma succ_succ_inj {a b : mynat} (h : S (S a) = S (S b)) : a = b.
Proof.
    exact (succ_inj (succ_inj h)).
Qed.

(* Level 2 *)
Lemma succ_eq_succ_of_eq {a b : mynat} : a = b -> S a = S b.
Proof.
    intro h.
    now rewrite h.
Qed.

(* Level 3 *)
Lemma eq_iff_succ_eq_succ (a b : mynat) : S a = S b <-> a = b.
Proof.
    split.
    - exact succ_inj.
    - exact succ_eq_succ_of_eq.
Qed.

(* Level 4 *)
Lemma add_right_cancel (a t b : mynat) : a + t = b + t -> a = b.
Proof.
    intro h.
    induction t as [| ? Ht].
    - setoid_rewrite add_zero in h.
      exact h.
    - repeat setoid_rewrite add_succ in h.
      inversion h.
      exact (Ht H0).
Qed.
