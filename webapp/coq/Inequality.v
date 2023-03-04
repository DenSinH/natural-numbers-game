From NaturalNumbers Require Export Base Tutorial Addition 
    Multiplication Power Proposition AdvProposition AdvAddition AdvMultiplication.

Definition le (a b : mynat) := exists (c : mynat), b = a + c.

Infix "<=" := le.
Notation "(<=)" := le (only parsing).
Notation "( f <=)" := (le f) (only parsing).
Notation "(<= f )" := (fun g => le g f) (only parsing).

Fact le_iff_exists_add (a b : mynat) : a <= b <-> exists (c : mynat), b = a + c.
Proof.
    split.
    - trivial.
    - trivial.
Qed.

(* Level 0 data *)
(* name `one_add_le_self` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
I have just added a new definition, that of `<=`. The statment
`a <= b` is defined to mean
```exists (c : mynat), b = a + c``` 
In other words, we can find some `c : mynat` such that `b = a + c`.

If you really want, you can use the lemma I have added,
```
#Fact le_iff_exists_add (a b : mynat) : a <= b <-> exists (c : mynat), b = a + c.
```
to rewrite `<=` into the `exists` statment, but it is not really necessary,
since Coq knows what `<=` means, so you can just treat it as if it is written
like the `exists` statement already.

Now how does one go about proving an `exists` statement? There is a tactic,
also called `exists`, that we can use. Basically, if we have to prove something
of the form 
`exists (c : mynat), 1 + x = x + c`,
typing `exists 1.` substitutes `1` for `c` in the equation, and turns our goal
into `1 + x = x + 1`. Now you can easily use the powerful `ring` tactic to
finish the proof. Try it yourself below!
*)
Lemma one_add_le_self (x : mynat) : x <= 1 + x.
Proof.
    exists 1.
    ring.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name `le_refl` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Here is an easy one, try using the `exists` tactic with
the right value for `c` to solve this one!
*)
Lemma le_refl (x : mynat) : x <= x.
Proof.
    exists 0.
    ring.
Qed.
(* Level epilogue *)
(*
Now we have shown that `<=` is a reflexive equation. 
I can now power up our `reflexivity` tactic, by typing
```
Require Import Coq.Classes.RelationClasses.

Global Instance le_Reflexive : Reflexive le := le_refl.
```
which allows us to prove statements like the following a lot
easier:
```
#Example refl : 0 <= 0.
#Proof.
#    reflexivity.
#Qed.
```
*)
(* Level end *)

Require Import Coq.Classes.RelationClasses.

Global Instance le_Reflexive : Reflexive le := le_refl.

Example refl : 0 <= 0.
Proof.
    reflexivity.
Qed.

(* Level 2 data *)
(* name `le_succ` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Okay, we have seen how goals with `exists` work, but what if we have
a hypothesis with an `exists` statement? Well, we can use our `destruct` 
tactic to obtain the variable that exists, and a witness for the statement
in the `exists` statement.

Basically, in this level, if we `intro h` we obtain `h : a <= b`. If we type
```
destruct h as [c H].
```
we obtain
```
c : mynat
H : b = a + c
```
Try it out below.
*)
Lemma le_succ (a b : mynat) : a <= b -> a <= S b.
Proof.
    intro h.
    destruct h as [c H].
    exists (S c).
    now rewrite H, add_succ.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `zero_le` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Another easy one.
*)
Lemma zero_le (a : mynat) : 0 <= a.
Proof.
    exists a.
    ring.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 data *)
(* name `le_trans` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Again, this one should not be too tough.
*)
Lemma le_trans (a b c : mynat) (hab : a <= b) (hbc : b <= c) : a <= c.
Proof.
    destruct hab as [ca ha].
    destruct hbc as [cb hb].
    rewrite ha in hb.
    exists (ca + cb).
    rewrite hb.
    ring.
Qed.
(* Level epilogue *)
(*
We have shown that `<=` is transitive. I can type the following
```
#Global Instance le_Transitive : Transitive le := le_trans.
#Global Instance le_PreOrder : PreOrder le.
#Proof.
#    constructor.
#    - exact le_Reflexive.
#    - exact le_Transitive.
#Qed.
```
to let Coq know that `<=` actually defines a preorder on `mynat`.
*)
(* Level end *)

Global Instance le_Transitive : Transitive le := le_trans.
Global Instance le_PreOrder : PreOrder le.
Proof.
    constructor.
    - exact le_Reflexive.
    - exact le_Transitive.
Qed.

(* Level 5 data *)
(* name `le_antisymm` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
In advanced addition world, we have shown 
```
#Lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a -> b = 0.
```
which might be useful here. Remember you can use `specialize` to create
new hypotheses out of ones you have, and theorems we have shown before.
So if we have `hd : a + (c + d) = a` and we want `h : c + d = 0`, you
can write 
```
specialize (eq_zero_of_add_right_eq_self hd) as h.
```
to do so.
*)
Lemma le_antisymm (a b : mynat) (hab : a <= b) (hba : b <= a) : a = b.
Proof.
    destruct hab as [ca ha].
    destruct hba as [cb hb].
    rewrite ha, add_assoc in hb.
    symmetry in hb.
    specialize (eq_zero_of_add_right_eq_self hb) as hcacb.
    specialize (add_right_eq_zero hcacb) as hca.
    rewrite hca, add_zero in ha.
    symmetry.
    exact ha.
Qed.
(* Level epilogue *)
(*
We have now shown that `<=` is a partial order! I typed
```
#Global Instance le_Antisymmetric : Antisymmetric _ _ le := le_antisymm.
#Global Instance le_PartialOrder : PartialOrder _ le.
#Proof.
#    constructor.
#    - intro h.
#      split; now exists 0.
#    - intro h.
#      destruct h as [h1 h2].
#      exact ((le_antisymm x x0) h1 h2).
#Qed.
```
to let Coq know it is.
*)
(* Level end *)


Global Instance le_Antisymmetric : Antisymmetric _ _ le := le_antisymm.
Global Instance le_PartialOrder : PartialOrder _ le.
Proof.
    constructor.
    - intro h.
      split; now exists 0.
    - intro h.
      destruct h as [h1 h2].
      exact ((le_antisymm x x0) h1 h2).
Qed.

(* Level 6 data *)
(* name `le_zero` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Remember the `symmetry` tactic? You can also use `symmetry`
in hypothesis by for example writing `symmetry in h` if
`h` is a hypothesis you have. It may come in useful in this level.
*)
Lemma le_zero (a : mynat) (h : a <= 0) : a = 0.
Proof.
    destruct h as [c h].
    symmetry in h.
    exact (add_right_eq_zero h).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 7 data *)
(* name `succ_le_succ` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Another straightforward one.
*)
Lemma succ_le_succ (a b : mynat) (h : a <= b) : S a <= S b.
Proof.
    destruct h as [c h].
    exists c.
    now rewrite h, succ_add.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 8 data *)
(* name `le_total` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Try using `revert a` to prove this one, otherwise you
might get stuck!
*)
Lemma le_total (a b : mynat) : a <= b \/ b <= a.
Proof.
    revert a.
    induction b as [| ? h].
    - intro a.
      right. exact (zero_le a).
    - intro a.
      destruct a.
      * left. exact (zero_le (S b)).
      * specialize (h a) as h.
        destruct h.
        + left. now apply succ_le_succ.
        + right. now apply succ_le_succ.
Qed.
(* Level epilogue *)
(* 
We have now shown that `<=` defines a linear order. Sadly
Coq does not have a builtin class for this.
*)
(* Level end *)

(* Total order? *)

(* Level 9 data *)
(* name `le_succ_self` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*  
It is possible to write a two line proof for this level!
*)
Lemma le_succ_self (a : mynat) : a <= S a.
Proof.
    rewrite succ_eq_add_one.
    now exists 1.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 10 data *)
(* name `add_le_add_right` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Remember to use the `intro` tactic on `forall` goals!
*)
Lemma add_le_add_right {a b : mynat} : a <= b -> forall (t : mynat), (a + t) <= (b + t).
Proof.
    intros h t.
    induction t as [| ? ht].
    - now simpl.
    - repeat rewrite add_succ.
      now apply succ_le_succ.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 11 data *)
(* name `le_of_succ_le_succ` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
Lemma le_of_succ_le_succ (a b : mynat) : S a <= S b -> a <= b.
Proof.
    intro h.
    destruct h as [c hc].
    rewrite succ_add in hc.
    exists c.
    now rewrite eq_iff_succ_eq_succ in hc.

    (* now inversion hc. *)
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 12 data *)
(* name `not_succ_le_self` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Remember to `unfold not` to turn negations `~P` into `P -> False`.
*)
Lemma not_succ_le_self (a : mynat) : ~(S a <= a).
Proof.
    unfold not.
    intro h.
    induction a as [| ? ha].
    - specialize (le_zero (S 0)) as h1.
      apply (succ_ne_zero 0).
      exact (h1 h).
    - apply ha.
      apply le_of_succ_le_succ.
      exact h.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 13 data *)
(* name `add_le_add_left` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
These levels may seem easy, but they are the things we need
to show that `mynat` is in fact an ordered commutative monoid.
*)
Lemma add_le_add_left {a b : mynat} (h : a <= b) (t : mynat) : t + a <= t + b.
Proof.
    rewrite add_comm, (add_comm t b).
    exact (add_le_add_right h _).
Qed.
(* Level epilogue *)
(* Level end *)

Definition lt (a b : mynat) := (a <= b) /\ ~(b <= a).

Infix "<" := lt.
Notation "(<)" := le (only parsing).
Notation "( f <)" := (le f) (only parsing).
Notation "(< f )" := (fun g => le g f) (only parsing).

(* Level 14 data *)
(* name `lt_aux_one` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
I have just introduced the definition of `<`. By definition,
`a < b` is the same as `(a <= b) /\ ~(b <= a)`. 
Remember to use the `destruct` tactic.
*)
Lemma lt_aux_one (a b : mynat) : a < b -> S a <= b.
Proof.
    intro h.
    destruct h as [hab hnba].
    destruct hab as [c habc].
    destruct c.
    - exfalso.
      rewrite add_zero in habc.
      apply hnba.
      rewrite habc.
      reflexivity.
    - rewrite habc.
      rewrite add_succ.
      exists c.
      now rewrite succ_add.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 15 data *)
(* name `lt_aux_two` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Now the other way.
*)
Lemma lt_aux_two (a b : mynat) : S a <= b -> a <= b /\ ~(b <= a).
Proof.
    intro h.
    split.
    - apply (le_trans a (S a) b); trivial.
      * exact (le_succ_self a).
    - unfold not.
      intro k.
      specialize (le_trans (S a) b a) as haSab.
      apply (not_succ_le_self a).
      now apply haSab.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 16 data *)
(* name `lt_iff_succ_le` *)
(* tactics exists *)
(* theorems le_iff_exists_add *)
(* Level prologue *)
(*
Alright, we can combine the previous levels 
(`lt_aux_one` and `lt_aux_two`) into this if and only
if statement, and then we have shown that `mynat` is an ordered
cancellative commutative monoid.
*)
Lemma lt_iff_succ_le (a b : mynat) : a < b <-> (S a) <= b.
Proof.
    split.
    - exact (lt_aux_one _ _).
    - exact (lt_aux_two _ _).
Qed.
(* Level epilogue *)
(*
That's it for the natural numbers game! If you enjoyed, feel
free to leave a star on the 
<a href="https://github.com/DenSinH/natural-numbers-game">source code on GitHub</a>.

I hope this helped you learn a bit about Coq and proof formalization.
*)
(* Level end *)
