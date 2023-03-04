From NaturalNumbers Require Export Base Tutorial Addition Multiplication AdvProposition.

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

(* Level 0 data *)
(* name `succ_inj`. A function. *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Peano's axioms actually included two more assumptions, which
we haven't seen (or used) yet:
<ul>
    <li>`Fact succ_inj {a b : mynat} : S a = S b -> a = b.`</li>
    <li>`Fact zero_ne_succ (a : mynat) : 0 <> S a.`</li>
</ul>
In the second statement, we see the `<>`, which is the "not equal" operator.
The reason they have not been introduced yet is that they are implications.

For `succ_inj a b` this is obvious, as there is an implication in the statement.
For the second statement it's a bit more subtle, as `zero_ne_succ a` actually means
```
0 = S a -> False.
``` 
Let's first learn to use `succ_inj` by using it to prove our own variant
of the statement: `succ_inj'`.
*)
Lemma succ_inj' {a b : mynat} (hs : S a = S b) : a = b.
Proof.
    exact (succ_inj hs).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name `succ_succ_inj` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
In this theorem, we will need to use the `succ_inj` axiom twice.
You can do it with `exact` (and maybe some `specialize` statements) or `apply`.
Try either way to get more used to these tactics!
*)
Lemma succ_succ_inj {a b : mynat} (h : S (S a) = S (S b)) : a = b.
Proof.
    exact (succ_inj (succ_inj h)).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name `succ_eq_succ_of_eq` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Now let's prove something completely obvious, using the same
input for the successor gives the same output. Remember our
rule of thumb about implications and the `intro` tactic,
and use it to prove this lemma!
*)
Lemma succ_eq_succ_of_eq {a b : mynat} : a = b -> S a = S b.
Proof.
    intro h.
    now rewrite h.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `eq_iff_succ_eq_succ` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Now let's combine our previous lemmas into an `<->` statement.
Remember the `split` tactic to prove the implications separately!

The first goal will be the same as `succ_inj`, so we can simply
`exact succ_inj.` to prove it. For the second goal we can do something
similar, but with the statement from the previous lemma.
*)
Lemma eq_iff_succ_eq_succ (a b : mynat) : S a = S b <-> a = b.
Proof.
    split.
    - exact succ_inj.
    - exact succ_eq_succ_of_eq.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 data *)
(* name `add_right_cancel` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Now we show that we can cancel on the right when doing addition,
i.e. that `a = b` whenever `a + t = b + t` for some `t`.

Now the `rewrite` tactic has some more magic to it. We can
rewrite theorems/hypothesis in <i>other hypotheses</i>!

If we `intro h.` in this level we get `h : a + t = b + t`.
Doing induction on `t` gives us hypotheses and a subgoal
```
a, b : mynat
h : a + 0 = b + 0
============================
a = b
```
now we can type 
```
rewrite add_zero in h.
```
to turn `h : a + 0 = b + 0` into `h : a = b`.
Try it out below!
*)
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
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name `add_left_cancel` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Using `add_comm`, you can rewrite `add_left_cancel` in a way that
allows us to simply `exact (add_right_cancel _ _ _).`, i.e. we can
tell Coq that `add_right_cancel` finishes off the goal, with three
paramters, which Coq can deduce by itself (denoted by the `_` wildcards).
*)
Lemma add_left_cancel (t a b : mynat) : t + a = t + b -> a = b.
Proof.
    rewrite add_comm, (add_comm t b).
    exact (add_right_cancel _ _ _).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `add_right_cancel_iff` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Similar to before, it may be useful to have an if and only if
statement, so we can `rewrite` it later on. Use the previous 
level (`add_right_cancel`) to show this if and only if statement.

Tip: if you type
```
exact (add_right_cancel _ _ _).
```
Coq will figure out what inputs to use by itself!
*)
Lemma add_right_cancel_iff (t a b : mynat) : a + t = b + t <-> a = b.
Proof.
    split.
    - exact (add_right_cancel _ _ _).
    - intro h.
      now rewrite h.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 7 data *)
(* name `eq_zero_of_add_right_eq_self` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
This next level will be useful later on in Inequality World, when
we will prove that `<=` is an antisymmetric relation.
*)
Lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a -> b = 0.
Proof.
    intro h.
    specialize (add_left_cancel a b 0) as h_simpl.
    rewrite (add_zero a) in h_simpl.
    exact (h_simpl h).
Qed.
(* Level epilogue *)
(* Level end *)

(* Unused 8 data *)
(* name `succ_ne_zero` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Unused prologue *)
(*
I don't want to use this level because it introduces
a new tactic that we are not going to use in other levels.
*)
Lemma succ_ne_zero (a : mynat) : S a <> 0.
Proof.
    (* todo: symmetry for <>? *)
    discriminate.
Qed.
(* Unused epilogue *)
(* Unused end *)

(* Level 8 data *)
(* name `add_left_eq_zero` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Inequalities `a <> b` in Coq are defined as `a = b -> False`.
So if you read `a <> b`, you should read it as `a = b -> False`.

The following lemma will be useful in Inequality World.
It will require a lot of the tactics you have learnt before,
like `destruct`, which similar to logical ors, we can use to
go over the cases of a natural number. In this level, it will be
useful to start with 
```
destruct b.
- ...
```
which will create two subgoals, one for `b = 0`, and one for `b = S n`
for some natural number `n : mynat`.

Also remember that any negations (like `~` but also `<>`) can be turned
into their `-> False` form by typing `unfold not`. In fact, we can also do
this in any hypotheses. Suppose we have `a b : mynat`, then we can
```
specialize (succ_ne_zero (a + b)) as snz.
```
to obtain a hypothesis
```
snz : S (a + b) <> 0.
```
If we then
```
unfold not in snz.
```
it gets turned into
```
snz : S (a + b) = 0 -> False.
```
which we may be able to use for an `exfalso` proof!

*)
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
(* Level epilogue *)
(* Level end *)

(* Level 9 data *)
(* name `add_right_eq_zero` *)
(* tactics exfalso *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Now that we know `add_left_eq_zero`, proving `add_right_eq_zero` should
not be too hard, especially knowing that addition is commutative,
witnessed by `add_comm`!
*)
Lemma add_right_eq_zero {a b : mynat} : a + b = 0 -> a = 0.
Proof.
    rewrite add_comm.
    apply add_left_eq_zero.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 10 data *)
(* name `add_one_eq_succ` *)
(* tactics symmetry *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
We know that `succ_eq_add_one (n : mynat) : S n = n + 1.`
but it may be useful to know it the other way around as well.
Did you know that for equalities, we can use the 
`symmetry` tactic to flip the sides of the goal?

Try it out below!
*)
Lemma add_one_eq_succ (d : mynat) : d + 1 = S d.
Proof.
    symmetry.
    exact (succ_eq_add_one _).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 11 data *)
(* name `ne_succ_self` (boss level!) *)
(* tactics symmetry *)
(* theorems zero_ne_succ *)
(* Level prologue *)
(*
Another boss level! Try to show that numbers
are not equal to their successor. Remember that
`unfold not` will turn negations and inequalities
into `-> False`!
*)
Lemma ne_succ_self (n : mynat) : n <> S n.
Proof.
    unfold not.
    induction n as [| ? h].
    - easy.
    - intro h1.
      now specialize (succ_inj h1) as h2.
Qed.
(* Level epilogue *)
(* Level end *)