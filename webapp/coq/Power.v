From NaturalNumbers Require Import Base Tutorial Addition Multiplication.

Fixpoint pow (a p : mynat) : mynat :=
    match p with
    | O => I
    | S q => (pow a q) * a
    end.

Infix "^" := pow.
Notation "(^)" := pow (only parsing).
Notation "( f ^)" := (pow f) (only parsing).
Notation "(^ f )" := (fun g => pow g f) (only parsing).

Fact pow_zero (a : mynat) : a ^ 0 = 1.
Proof.
    (* unfold pow *)
    trivial.
Qed.

Fact pow_succ (a b : mynat) : a ^ S b = a ^ b * a.
Proof.
    (* unfold pow *)
    trivial.
Qed.

(* Level 0 *)
Lemma zero_pow_zero : 0 ^ 0 = 1.
Proof.
    (* unfold pow *)
    reflexivity.
Qed.

(* Level 1 *)
Lemma zero_pow_succ (m : mynat) : 0 ^ S m = 0.
Proof.
    (* probably best to do this with induction over m for practice though *)
    reflexivity.
Qed.

(* Level 2 *)
Lemma pow_one (a : mynat) : a ^ 1 = a.
Proof.
    rewrite one_eq_succ_zero.
    rewrite pow_succ.
    rewrite pow_zero.
    ring.
Qed.

(* Level 3 *)
Lemma one_pow (m : mynat) : 1 ^ m = 1.
Proof.
    induction m as [| ? H].
    - reflexivity.
    - rewrite pow_succ.
      rewrite H.
      reflexivity.
Qed.

(* Level 4 *)
Lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n.
Proof.
    induction n as [| ? H].
    - rewrite pow_zero.
      ring_simplify.
      reflexivity.
    - rewrite add_succ.
      repeat rewrite pow_succ.
      rewrite H.
      ring.
Qed.

(* Level 5 *)
Lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n.
Proof.
    induction n as [| ? H].
    - reflexivity.
    - repeat rewrite pow_succ.
      rewrite H.
      ring.
Qed.

(* Level 6 *)
Lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n).
Proof.
    induction n as [| ? H].
    - repeat rewrite pow_zero; easy.
    - rewrite mul_succ, pow_succ, pow_add.
      rewrite H.
      reflexivity.
Qed.

Definition II := S I.
Notation "2" := II.
Fact two_eq_succ_one : 2 = S 1.
Proof.
  trivial.
Qed.

(* Level 7 *)
Lemma add_squared (a b : mynat) : (a + b) ^ 2 = a^2 + b^2 + 2 * a * b.
Proof.
    (* rewrite two_eq_succ_one *)
    unfold II, I.
    repeat rewrite pow_succ.
    repeat rewrite pow_zero.
    repeat rewrite one_mul.
    rewrite mul_add, add_mul.
    rewrite add_mul.
    repeat rewrite succ_mul.
    (* ring_simplify.  output is ugly *)
    ring.
Qed.

