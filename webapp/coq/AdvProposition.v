(* Level 0 data *)
(* name the `split` tactic *)
(* tactics split *)
(* Level prologue *)
(*
In this world we will learn about the tactics `split`,
`destruct`, `left`, `right` and `exfalso`. These are 
some of the last tactics you will need to beat the game.

The logical symbol `/\` means "and", so if our goal is
`P /\ Q` we effectively have to prove both `P` and `Q`.
In order to do this, we use the `split` tactic to
`split` our goal up into two subgoals. We can then
use dashes `-` to solve for `P` and `Q` individually,
in this case with the `exact` tactic.
*)
Example prop_and (P Q : Prop) (p : P) (q : Q) : P /\ Q.
Proof.
    split; assumption.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name the `destruct` tactic *)
(* tactics destruct *)
(* Level prologue *)
(*
So we can use `split` to solve goals of the form 
`P /\ Q`, but what if we have a hypothesis of the form
`P /\ Q`? In this case we can `destruct` it into two
separate hypotheses, witnessing each branch of the logical
and respectively. So in this level, an obvious first move is
to 
```
intro h.
```
which leaves us with `h : P /\ Q` to prove `Q /\ P`. We can
```
destruct h as [p q].
```
to obtain `p : P` and `q : Q`. The rest of the level should
be easy with the `split` tactic we learnt before.
*)
Lemma and_symm (P Q : Prop) : P /\ Q -> Q /\ P.
Proof.
    intro h.
    destruct h as [p q].
    split; assumption.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name `and_trans` *)
(* tactics destruct *)
(* Level prologue *)
(*
Try using the tactics you learnt before to solve this
by yourself. By the way, did you know that if you 
have a hypothesis `h : P /\ Q` and you type
```
destruct h as [p _].
```
you only obtain `p : P`, and no hypothesis for `Q`? Similarly,
if you type 
```
destruct h as [p ?].
```
we obtain `p : Q`, and some hypothesis for `Q`, though the name depends
on the context. Though for this level, the `_` wildcard might come in
more useful.
*)
Lemma and_trans (P Q R : Prop) : P /\ Q -> Q /\ R -> P /\ R.
Proof.
    intros h1 h2.
    destruct h1 as [p _].
    destruct h2 as [_ r].
    split; assumption.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `iff_trans` *)
(* tactics destruct *)
(* Level prologue *)
(*
A mathematical statement of the form `P <-> Q` is equivalent
to `(P -> Q) /\ (Q -> P)`. The `split` and `destruct` tactics
work on `<->` as if it was typed like that. Try them out
in this level!
*)
Lemma iff_trans (P Q R : Prop) : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros h1 h2.
    destruct h1 as [pq qp].
    destruct h2 as [qr rq].
    split.
    - intro p. exact (qr (pq p)).
    - intro r. exact (qp (rq r)).
Qed.
(* Level epilogue *)
(* Level end *)

(* Lean has alternate notation to destruct (/case in lean) and a level for this *)
(* This is also interesting though *)
Require Import Setoid.

(* Level 4 data *)
(* name `iff_trans` easter eggs *)
(* tactics destruct *)
(* Level prologue *)
(*
Let's try that level again, but then in a different way.
Instead of `destruct`ing our hypothesis `h : P <-> Q`, we can
also use it to `rewrite` our goal, similar to how it worked for
equalities. For this level, try to type 
```
intros h1 h2.
rewrite h1.
```
to see what happens!
*)
Lemma iff_trans2 (P Q R : Prop) : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros h1 h2.
    rewrite h1, h2.
    reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name Or, and the `left` and `right` tactics *)
(* tactics left / right *)
(* available false *)
(* Level prologue *)
(*
`P \/ Q` means `P` or `Q`. If we wish to prove a goal of this
form, we need to prove either `P` or `Q`. You can use the 
`left` tactic to transform the goal into `P`, and similarly
the `right` tactic to transform it into `Q`. use `intro` and
choose the correct tactic to `exact` our hypothesis and finish
the proof. Be careful, if you choose the wrong tactic out of
`left` and `right`, we end up with a goal that is
impossible to prove!
*)
Example prop_or (P Q : Prop) : Q -> (P \/ Q).
Proof.
    intro q.
    right.
    exact q.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `or_symm` *)
(* tactics left / right *)
(* Level prologue *)
(*
Proving that `(P \/ Q) -> (Q \/ P)` may be a bit tricky.
We obtain a hypothesis of the form `h : P \/ Q` if we do
`intro h`, but we need to prove either `Q` or `P` if we 
type `left` or `right`, not `P \/ Q`... Fortunately, we
can use the `destruct` tactic to perform case analysis on `h`.

Type 
```
intro h.
destruct h as [p|q].
```
and you will transform our goal into two subgoals, one
where we get `p : P` in our assumptions, and one where
we get `q : Q` in our assumptions. Note again that we can 
use the `_` and `?` wildcards between the brackets `[]` here,
but this is not very useful, and might even make it impossible to 
prove. 

To denote that you are working on a subgoal, again use the dashes
`-`. 
*)
Lemma or_symm (P Q : Prop) : (P \/ Q) -> (Q \/ P).
Proof.
    intro h.
    (* Performs case analysis on h *)
    destruct h as [p|q].
    - right; exact p.
    - left; exact q.
Qed.
(* Level epilogue *)
(* Level end *)


(* Level 7 data *)
(* name `and_or_distrib_left` *)
(* tactics left / right *)
(* Level prologue *)
(*
In this level, you will need to use the `split` and
`destruct` tactics a lot. Now, you might be in a scenario
where you have multiple nested subgoals. In this case,
you should no longer just use `-`, but also `*`, then `+`,
then `--`, then `**`, etc.

Basically, you can start this proof of like so
```
split.
- intro h.
  destruct h as [p qr].
  destruct qr as [q|r].
  * left.
    split.
    + exact p.
    ...
```
see what I mean?

Try it out below!
*)
Lemma and_or_distrib_left (P Q R : Prop) : P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
    tauto.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 8 data *)
(* name `exfalso` and proof by contradiction *)
(* tactics exfalso *)
(* available false *)
(* Level prologue *)
(*
*whispers tell them about `tauto`...

Alright, alright... There is a very powerful tactic called `tauto`.
You can use it to solve logical goals very easily. It will work
for this level, and even for the previous level with the many cases!

Try not to use it too much though, as in this level we will also practice
with another, more basic tactic: `exfalso`.
This tactic turns any current subgoal into `False`, since if we know
that if `False` is true, we can conclude anything! Sounds weird right...

Anyway, in this level, you are able to obtain hypothesis `P` and `~P`
(or `P -> False`, see where we are going?). Regardless of what your
goal is at that point (probably `Q`), you can type `exfalso` to turn our
goal into `False`. At that point, if you have a hypothesis `np : ~P`, we 
can `rewrite np` to turn our goal into `P` and you are able to `exact` 
another hypothesis to finish the proof! 
*)
Lemma contra (P Q : Prop) : (P /\ ~P) -> Q.
Proof.
    tauto.
Qed.
(* Level epilogue *)
(* Level end *)

(* Law of excluded middle, this is not really very HoTT *)
Theorem LEM (P : Prop) : P \/ ~P.
Proof.
    admit.
Admitted.

(* Level 9 data *)
(* name the law of the excluded middle *)
(* tactics exfalso *)
(* available false *)
(* Level prologue *)
(*
In this level we are going to assume something that
we commonly don't in homotopy type theory: the law of the excluded middle.
The statement is 
```
Axiom LEM : forall (P : Prop), P \/ ~P.
```
effectively telling us that for any proposition `P`, either
`P` holds, or `~P` holds. Try to prove the following lemma,
witnessing that contrapositive proofs work, using this axiom.
Remember that you might have to 
```
specialize (LEM X) as lx.
```
with some proposition `X` to do anything useful with it.
Also remember the order of the dashes: (`-`, then `*`, then `+`,
then double, triple etc.)
*)
Lemma contrapositive (P Q : Prop) : (~Q -> ~P) -> (P -> Q).
Proof.
    unfold not.
    intros h p.
    specialize (LEM Q) as lq.
    destruct lq as [q|nq].
    - exact q.
    - exfalso.
      apply h; assumption.
Qed.
(* Level epilogue *)
(* Level end *)

