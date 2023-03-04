From NaturalNumbers Require Export Base Tutorial.

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

(* Level 0 data *)
(* name The `induction` tactic *)
(* tactics induction *)
(* theorems add_succ *)
(* Level 0 prologue *)
(*
Alright, so now that we know the basics, let's get started with addition.
Just as a reminder, these are the things we have and know:
<ul>
  <li>a type `mynat`</li>
  <li>a term `0 : mynat`, the number zero</li>
  <li>a function `S: mynat -> mynat` taking a number `n` to its successor</li>
  <li>addition, with the usual notation `a + b`</li>
  <li>a theorem `add_zero (n : mynat) : n + 0 = n.`</li>
  <li>a theorem `add_succ (m n : mynat) : n + (S m) = S (n + m).`</li>
  <li>the principle of mathematical induction, used with the `induction` tactic, see below.</li>
</ul>

Okay, so in this first level we will prove
```
#Lemma zero_add (n : mynat) : 0 + n = n.
```
Strange right, it seems so simple knowing our theorem
```
#Fact add_zero (n : mynat) : n + 0 = n.
```
but commutativity is not a given! To prove the lemma for this level,
just `rewrite` and `reflexivity` are not enough, we need something stronger.
There is a tactic called `induction`, which we can use on inductive types
like our type `mynat`. Suppose we have a `n : mynat` in our assumptions, then
we can write
```
induction n s [| ? h].
```
to start our induction proof. When you type this, Coq will start
two "subgoals", one for the base case (`n = 0`), and one for the 
induction step. It is common practice to "select" the subgoal explicitly
by typing a dash `-` on the next line. Doing this you will only see one goal again.
Once you are done proving this goal, the interpreter will tell you
```
This subproof is complete, but there are some unfocused goals.
Focus next goal with bullet -.

1 subgoal

subgoal 1 is:
...
```
Now you might wonder what the `[| ? h]` means. To be very precise, in
our inductive type `mynat` we have two constructors (`0` and `S n`), so `induction`
will produce two paths. In the first path, we don't get any (new) hypotheses, so we 
don't have to name any variables. In the second path, we get a number and an induction
hypothesis. The `?` is the name for the number, indicating we don't really care
what it is called, we well see it in the subgoal (it will be `n`, the same name as
the variable we are doing induction over). The second hypothesis is the induction
hypothesis. I always like to call it `h`, I think by default it is `IHn`.
This variable will be the induction hypothesis, saying `h : 0 + n = n`.

In short, the proof will look something like this:
```
induction n as [| ? h].
- rewrite ...
  ...
  reflexivity.
- rewrite ...
  ...
  reflexivity.
```
Try it out below!
*)
Lemma zero_add (n : mynat) : 0 + n = n.
Proof.
    induction n as [| ? H].
    - rewrite add_zero.
      reflexivity.
    - rewrite add_succ.
      rewrite H.
      reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name `add_assoc` -- associativity of addition *)
(* tactics induction *)
(* theorems add_succ *)
(* Level 1 prologue *)
(*
The next step is to prove that addition is associative, i.e. that
`(a + b) + c = a + (b + c)`. Note that in the goals, the left
hand side of the equation will show up as `a + b + c` instead
of `(a + b) + c`. This is simply because Coq knows that 
addition is left-binding.
*)
Lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c).
Proof.
    induction c as [| ? H].
    - repeat rewrite add_zero.
      reflexivity.

      (* This only works if we do induction on C, otherwise we would want succ_add *)
    - repeat rewrite add_succ.
      rewrite H.
      reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name `succ_add` *)
(* tactics repeat *)
(* theorems add_succ *)
(* Level 2 prologue *)
(*
It is almost time for the boss level of this world. Before that,
let us first prove the counterpart to `add_succ`: `succ_add`.
Just as a tip, instead of repeatedly writing `rewrite add_zero.`, it
is also possible to use the `repeat` tactic, allowing you to write 
```
repeat rewrite add_zero.
```
When using the `rewrite` tactic, Coq guesses which parameters to use
in the theorem. It is also possible to do this explicitly by writing
```
rewrite (add_zero a)
```
to rewrite a subterm `a + 0` into `a`.
*)
Lemma succ_add (a b : mynat) : S a + b = S (a + b).
Proof.
  induction b as [| ? H].
  - repeat rewrite add_zero.
    reflexivity.
  - repeat rewrite add_succ.
    rewrite H.
    reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `add_comm` (boss level) *)
(* tactics repeat *)
(* theorems add_succ *)
(* Level 3 prologue *)
(*
<b>*boss music*</b>

Check the side menu to remember the theorems you have shown so far,
you should be prepared to prove this lemma.
*)
Lemma add_comm (a b : mynat) : a + b = b + a.
Proof.
  induction b as [| ? H].
  - now rewrite add_zero, zero_add.
  - rewrite add_succ, succ_add.
    now rewrite H.
Qed.
(* Level epilogue *)
(* Level end *)

(* Given in natural numbers game *)
Definition I := S 0.
Notation "1" := I.
Fact one_eq_succ_zero : 1 = S 0.
Proof.
  trivial.
Qed.

(* Level 4 data *)
(* name `succ_eq_add_one` *)
(* tactics repeat *)
(* theorems one_eq_succ_zero *)
(* Level 4 prologue *)
(*
I have just defined the number `1`, in the way you would 
expect: `1 = S 0`, and added a theorem
```
#Fact one_eq_succ_zero : 1 = S 0.
```
that witnesses this. Use it to prove the following theorem.
*)
Lemma succ_eq_add_one (n : mynat) : S n = n + 1.
Proof.
  rewrite one_eq_succ_zero.
  rewrite add_succ.
  rewrite add_zero.
  reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name `add_right_comm` *)
(* tactics repeat *)
(* theorems one_eq_succ_zero *)
(* Level 5 prologue *)
(*
Alright, time for the last level in Addition World.
Here it might be useful to use the strategy I mentioned before:
rewriting a specific term in the equation. Remember you can do this
with the `rewrite` tactic by using it like this:
```
rewrite (add_comm b c).
```
*)
Lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b.
Proof.
  rewrite add_assoc.
  rewrite (add_comm b c).
  (* Can just use the forward direction but whatever *)
  rewrite <- add_assoc.
  reflexivity.
Qed.
(* Level epilogue *)
(*
With all these statements about addition, we have shown that
`mynat` is a commutative monoid. In Lean (the proof checker
from the original Natural Numbers Game) we could tell the 
proof checker that `mynat` is indeed a commutative monoid.
Sadly such a structure does not exist, but I have come up with a
(rather hacky) solution for this, so that we can still use some
more advanced tactics to make your life easier. 

Basically, I added a "fake" multiplication operation, and 
added some `Axiom`s (basically theorems which we just assume to be 
true, do this at your own risk!). With these, I was able to convince
Coq that `mynat` is a semiring with this fake multiplication. For now
this will suffice, and it allows us to use the powerful `ring` tactic,
allowing us to prove simple statements about expressions in one line,
such as
```
#Lemma test (a b c d e : mynat) : (((a+b)+c)+d)+e=(c+((b+e)+a))+d.
#Proof.
#    ring.
#Qed.
``` 

It is now time to move on to Multiplication World! Though if you wish,
you could also go to Function World, as we know enough to get started
there too. You can do this by going back to the main menu and clicking 
Function World in the graph!
*)
(* Level end *)
