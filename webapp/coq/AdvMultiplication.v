From NaturalNumbers Require Export Base Tutorial Addition Multiplication Power AdvAddition.

(* Level 0 data *)
(* name `mul_pos` *)
(* tactics symmetry *)
(* Level prologue *)
(*
Welcome to Advanced Multiplication World! It is strongly
recommended that you have finished the worlds before this one,
so that you are familiar with the tactics we introduced there.

Remember that if you have a natural number `n : mynat`, you
can use `destruct n.` to perform case analysis on the cases
where `n = 0` and where `n = S k` for some `k : mynat`. It's
kind of like a weaker form of `induction`.
*)
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
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name `eq_zero_or_eq_zero_of_mul_eq_zero` *)
(* tactics symmetry *)
(* Level prologue *)
(*
A variant on the previous level.
*)
Lemma eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) : a = 0 \/ b = 0.
Proof.
    destruct a.
    - left; easy.
    - right.
      rewrite (succ_mul a b) in h.
      specialize (add_left_eq_zero h) as h1.
      exact h1.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name `mul_eq_zero_iff` *)
(* tactics symmetry *)
(* Level prologue *)
(*
After the previous two levels, this one should be pretty straight forward.
*)
Lemma mul_eq_zero_iff (a b : mynat) : a * b = 0 <-> a = 0 \/ b = 0.
Proof.
    split.
    - exact (eq_zero_or_eq_zero_of_mul_eq_zero _ _).
    - intros h.
      destruct h as [h|h].
      * now rewrite h, zero_mul.
      * now rewrite h, mul_zero.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `mul_left_cancel` (boss level!) *)
(* tactics revert *)
(* Level prologue *)
(*
This is a pretty tough level. I will admit that I struggled with it a 
bit myself as well. It requires a pretty advanced technique. If you just
run at it, and try to use induction on any of the variables, you will get
stuck in the induction step. If you do this, the induction step will 
give you an induction hypothesis `a * b = a * c -> b = c`, but
it wants you to prove that `a * b = a * S c -> b = S c`. Here,
your induction hypothesis will be useless!

Instead, we have to use the `revert` tactic. This tactic is kind
of the opposite of the `intro` tactic. It removes one of our hypotheses,
and turns the rest of the hypotheses and the goal into `forall` statments. 
I.e., if we have 
```plaintext
a, b, c : mynat
ha : a <> 0
============================
a * b = a * c -> b = c
```
and we type `revert b.`, we get
```plaintext
a, c : mynat
ha : a <> 0
============================
forall b : mynat, a * b = a * c -> b = c
```
Now this is a statement we can prove by induction over `c`!

Try to start off your proof with
```
revert b.
induction c as [| ? h].
```
and you should be able to finish the rest, though it might be tough!
*)
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
(* Level epilogue *)
(* Level end *)