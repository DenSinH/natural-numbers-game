From NaturalNumbers Require Import Base Tutorial Addition Multiplication.

Require Coq.Classes.RelationClasses.

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
Lemma add_right_cancel (a b t : mynat) : a + t = b + t -> a = b.
Proof.
    intro h.
    induction t as [| ? Ht].
    - rewrite add_zero in h.
      exact h.
    - repeat rewrite add_succ in h.
      inversion h.
      exact (Ht H0).
Qed.

(* Level 5 *)
Lemma add_left_cancel (t a b : mynat) : t + a = t + b -> a = b.
Proof.
    rewrite add_comm, (add_comm t b).
    exact (add_right_cancel _ _ _ ).
Qed.

(* Level 6 *)
Lemma add_right_cancel_iff (t a b : mynat) : a + t = b + t <-> a = b.
Proof.
    split.
    - exact (add_right_cancel _ _ _).
    - intro h.
      now rewrite h.
Qed.

(* Level 7 *)
Lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a -> b = 0.
Proof.
    intro h.
    specialize (add_left_cancel a b 0) as h_simpl.
    rewrite (add_zero a) in h_simpl.
    exact (h_simpl h).
Qed.

(* Level 8 *)
Lemma succ_ne_zero (a : mynat) : S a <> 0.
Proof.
    (* todo: symmetry for <>? *)
    discriminate.
Qed.

(* Level 9 *)
Lemma add_left_eq_zero {a b : mynat} (h : a + b = 0) : b = 0.
Proof.
    destruct b.
    - reflexivity.
    - exfalso.
      rewrite add_succ in h.
      specialize (succ_ne_zero (a + b)) as snz.
      unfold not in snz.
      exact (snz h).
Qed.

(* Level 10 *)
Lemma add_right_eq_zero {a b : mynat} : a + b = 0 -> a = 0.
Proof.
    rewrite add_comm.
    apply add_left_eq_zero.
Qed.

(* Level 11 *)
Lemma add_one_eq_succ (d : mynat) : d + 1 = S d.
Proof.
    symmetry.
    exact (succ_eq_add_one _).
Qed.

(* Level 12 *)
Lemma ne_succ_self (n : mynat) : n <> S n.
Proof.
    unfold not.
    induction n as [| ? h].
    - easy.
    - intro h1.
      now specialize (succ_inj h1) as h2.
Qed.
