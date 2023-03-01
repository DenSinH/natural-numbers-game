From NaturalNumbers Require Import Base Tutorial Addition Multiplication Power AdvAddition.

(* Level 0 *)
Lemma mul_pos (a b : mynat) : a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
    intros h k l.
    unfold not in *.
    destruct a.
    - now apply h.  (* convert False to 0 = 0 *)
    - rewrite succ_mul in l.
      specialize (add_left_eq_zero l) as h1.
      exact (k h1).
Qed.

(* Level 1 *)
Lemma eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) : a = 0 \/ b = 0.
Proof.
    destruct a.
    - left; easy.
    - right.
      rewrite (succ_mul a b) in h.
      specialize (add_left_eq_zero h) as h1.
      exact h1.
Qed.

(* Level 2 *)
Lemma mul_eq_zero_iff (a b : mynat) : a * b = 0 <-> a = 0 \/ b = 0.
Proof.
    split.
    - exact (eq_zero_or_eq_zero_of_mul_eq_zero _ _).
    - intros h.
      destruct h as [h|h].
      * now rewrite h, zero_mul.
      * now rewrite h, mul_zero.
Qed.

(* Level 3 *)
Lemma mul_left_cancel (a b c : mynat) (ha : a <> 0) : a * b = a * c -> b = c.
Proof.
    revert b.
    induction c as [| ? h].
    - intro b.
      rewrite mul_zero.
      intro h1.
      rewrite (mul_eq_zero_iff a b) in h1.
      destruct h1 as [|H].
      * contradiction.
      * exact H.
    - intros b h2.
      destruct b.
      * rewrite mul_zero in h2.
        symmetry in h2.
        rewrite mul_eq_zero_iff in h2.
        destruct h2.
        + contradiction.
        + now symmetry.
      * apply succ_eq_succ_of_eq.
        repeat rewrite mul_succ in h2.
        rewrite add_right_cancel_iff in h2.
        exact ((h b) h2).
Qed.