From NaturalNumbers Require Export Base Tutorial Addition Multiplication.

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

(* Level 0 data *)
(* name `zero_pow_zero` *)
(* tactics induction *)
(* theorems pow_succ *)
(* Level 0 prologue *)
(*
Power world it is! Let's define our power operator on `mynat` real quick, 
and give you the following theorems to work with:
<ul>
    <li>`Fact pow_zero (a : mynat) : a ^ 0 = 1.`</li>
    <li>`Fact pow_succ (a b : mynat) : a ^ S b = a ^ b * a.`</li>
</ul>
We will not be needing any additional tactics in this world, 
`rewrite`, `reflexivity` and `induction` should be enough, though
the `ring` tactic might come in handy!

I will leave you at it for this world, with all the theorems you
have so far you should be able to handle yourself without any
hints or tips from me!
*)
Lemma zero_pow_zero : 0 ^ 0 = 1.
Proof.
    (* unfold pow *)
    reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name `zero_pow_succ` *)
(* tactics induction *)
(* theorems pow_succ *)
(* Level 1 prologue *)
Lemma zero_pow_succ (m : mynat) : 0 ^ S m = 0.
Proof.
    (* probably best to do this with induction over m for practice though *)
    reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name `pow_one` *)
(* tactics induction *)
(* theorems pow_succ *)
(* Level 2 prologue *)
Lemma pow_one (a : mynat) : a ^ 1 = a.
Proof.
    rewrite one_eq_succ_zero.
    rewrite pow_succ.
    rewrite pow_zero.
    ring.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `one_pow` *)
(* tactics induction *)
(* theorems pow_succ *)
(* Level 3 prologue *)
Lemma one_pow (m : mynat) : 1 ^ m = 1.
Proof.
    induction m as [| ? H].
    - reflexivity.
    - rewrite pow_succ.
      rewrite H.
      reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 data *)
(* name `pow_add` *)
(* tactics induction *)
(* theorems pow_succ *)
(* Level 4 prologue *)
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
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name `mul_pow` *)
(* tactics induction *)
(* theorems pow_succ *)
(* Level 5 prologue *)
Lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n.
Proof.
    induction n as [| ? H].
    - reflexivity.
    - repeat rewrite pow_succ.
      rewrite H.
      ring.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `pow_pow` (boss level!) *)
(* tactics induction *)
(* theorems pow_succ *)
(* Level 6 prologue *)
(*
Boss level! Alright, maybe a quick tip about the `rewrite` tactic.
Did you know that instead of repeatedly writing `rewrite` with different
theorems or hypotheses like so:
```
rewrite succ_add.
rewrite mul_succ.
rewrite mul_add.
...
```
you can instead do
```
rewrite succ_add, mul_succ, mul_add.
```
Try it out!
*)
Lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n).
Proof.
    induction n as [| ? H].
    - repeat rewrite pow_zero; easy.
    - rewrite mul_succ, pow_succ, pow_add.
      rewrite H.
      reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

Definition II := S I.
Notation "2" := II.
Fact two_eq_succ_one : 2 = S 1.
Proof.
  trivial.
Qed.

(* Level 7 data *)
(* name `add_squared` *)
(* tactics induction *)
(* theorems two_eq_succ_one *)
(* Level 7 prologue *)
(*
I have just added the definition for 2 (yeah, we didn't
have that yet...) and a theorem 
```
#Fact two_eq_succ_one : 2 = S 1.
```
Use it to prove the last theorem of Power World!
*)
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
(* Level epilogue *)
(* Level end *)
