From NaturalNumbers Require Export Base.

(* Level 0 data *)
(* name The `reflexivity` tactic *)
(* tactics reflexivity *)
(* theorems null *)
(* available false *)
(* Level 0 prologue *)
(* 
```
From NaturalNumbers Require Export Base.
(* With this we import the definition for mynat *)
```
Let's start off learning some tactics. The simplest tactic is `reflexivity`,
which basically just proves any statement of the form `x = x`. It might 
deduce some very basic simplifications if the type of `x` allows for it, 
but since we are working with `mynat`, which has no structure whatsoever
(as far as we have shown!), it will basically only work for <i>exactly equal</i>
statements. So `x * y + z = x * y + z` will be proven by `reflexivity`, but
`x + y = y + x` will not.

Each level in this game involves a `Lemma` to be shown (sometimes I made it
an `Example` if the statement is not useful in the future). It is your task to
prove these lemmas using the tactics we learn and theorems we prove along the way.

In Coq, every time you use a tactic, you finish it off with a period (`.`).
If you do not type this period, the interpreter will think you are still busy
writing out your proof, and won't do its job, so make sure not to forget it!

For this first level, try to type `reflexivity.` in the editor, and see what happens.
When the compiler tells you `No more subgoals.`, the proof is complete.

If you forget what tactics do, you can use the left-hand dropdown to look it up.
When you are done with this level, the top of the screen should turn green to 
indicate you finished your proof. When you have finished all the levels in this world,
it will turn green in the main menu. 
*)
Example refl (x y : mynat) : x + x + y = x + x + y.
Proof.
    reflexivity.
Qed.
(* Level epilogue *)
(* Level 0 end *)


(* Level 1 data *)
(* name The `rewrite` tactic *)
(* tactics rewrite *)
(* theorems null *)
(* available false *)
(* Level 1 prologue *)
(*
The `rewrite` tactic allows us to "substitute" variables.
If you have a hypothesis of the form `A = B`, like `h` below,
you can use the tactic `rewrite h.` to replace any occurence of
`A` with `B` in the current (sub)goal. Note that this, like the
`reflexivity` tactic, expects the right hand side to occur <i>exactly</i>
like it shows up in the hypothesis, or the interpreter will give an error.

For the example below, we have a hypothesis `h` witnessing that 
`x = y + z`, so when we `rewrite h.` we will replace all occurences 
of `x` with `y + z` in the goal. Try it out below, and don't forget the period!
*)
Example rewr (x y z : mynat) (h : x = y + z) : x + z = y + z + z.
Proof.
    rewrite h.
    reflexivity.
Qed.
(* Level 1 epilogue *)
(*
<h2>Exploring your proof</h2>
You can go navigate the editor (either with the arrow keys or the mouse), and
you will see the state of the proof up to your cursor. Note that 
if you finish writing your proof in the middle, the server never sees your
full proof, so it will not know that you finished it. In short: if you are done
with your proof, make sure to navigate to the end of it and wait until you see
that the interpreter verified your proof (with the `No more subgoals.` message).

<h4>Resources on tactics</h4>
The tactics explorer on the left hand side is fairly basic, but there is much
more information available online. For example in the 
<a href="https://coq.inria.fr/refman/coq-tacindex.html">official Coq documentation</a>.
Check it out if you wish to know more, or if you want to find other tactics you can
use by yourself!
*)
(* Level 1 end *)


(* Level 2 data *)
(* name The `rewrite` tactic *)
(* tactics rewrite *)
(* theorems null *)
(* available false *)
(* Level 2 prologue *)
(*
Now that we have learnt our first basic tactics, let's take a look
at our implementation of the natural numbers (`mynat`). This is an "inductive type",
defined with two constructors: the number 0, and a function
`S : mynat -> mynat`, giving for each number `n : mynat` its successor `S n : mynat`.

There are some axioms on the natural numbers by Peano which uniquely characterise them,
two of which correspond exactly with the definitions given above. The last axiom is that
of mathematical induction, stating that we can prove something about the natural numbers
if we can show it for 0 and if we can deduce it for `S n` given that we know it for `n`.
One cool thing about Coq is that if we define our natural numbers, it will automatically
define this principle for us!

For now we will not worry about that yet, let's practice with our `rewrite` and `reflexivity` 
tactics a bit first. Did you know that it is possible to rewrite the right hand side of a
hypothesis as well by typing `rewrite <- h.`? Try it out below!
*)
Example peano (a b : mynat) (h : S a = b) : S a = b.
Proof.
    rewrite <- h.
    reflexivity.
Qed.
(* Level 2 epilogue *)
(*
For those interested, the exact implementation of `mynat` is 
```
Inductive mynat : Set :=
  | O : mynat
  | S : mynat -> mynat.
```
*)
(* Level 2 end *)

(* Given statements in Natural Numbers Game in Lean.
   They just write that Peano gave these.
   If we really wanted we could have just Admitted. them *)
Fact add_zero (n : mynat) : n + 0 = n.
Proof.
    trivial.
Qed.

Fact add_succ (m n : mynat) : n + (S m) = S (n + m).
Proof.
    trivial.
Qed.

(* Level 3 data *)
(* name The `rewrite` tactic *)
(* tactics rewrite *)
(* theorems add_succ *)
(* available false *)
(* Level 3 prologue *)
(*
Just writing `0`, `S 0`, `S (S 0)` etc. becomes a bit boring, so let's 
introduce addition! Peano defined this by "recursion". He described how
to add 0 to a number, the base case:
```Fact add_zero (n : mynat) : n + 0 = n.```
and then what happens if you add the successor of any number to another number
(the inductive step):
```Fact add_succ (m n : mynat) : n + (S m) = S (n + m).```
Coq defined recursion on our inductive type `mynat` for us, so it was possible
to define it in this way. The `Fact` keyword does not mean much by the way,
it is effectively just an alias for `Lemma`, and these two "facts" are effectively
the definition for addition, so their proofs are just one line.

We can use these theorems in our proofs though, try to `rewrite` them below
by typing `rewrite add_succ.` Then use `add_zero` and `reflexivity` to prove
the statement.
*)
Lemma add_succ_zero (a : mynat) : a + S 0 = S a.
Proof.
    rewrite add_succ.
    rewrite add_zero.
    reflexivity.
Qed.
(* Level 3 epilogue *)
(*
That was it for the tutorial, let's move on to Addition World, where we get started
with induction, and proving interesting results.
*)
(* Level 3 end *)