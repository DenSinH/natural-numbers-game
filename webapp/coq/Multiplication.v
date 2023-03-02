From NaturalNumbers Require Export Base Tutorial Addition.

Require Import Ring_theory.
Require Export Ring.

Module SemiRingFaking.
    (* Some stuff to fake the `simpl` tactic to only affect
    our own version of addition by defining some sort of fake 
    multiplication and a bunch of axioms to make the semi-ring 
    structure hold *)

    Axiom _fake_mul : mynat -> mynat -> mynat.
    Axiom _fake_one : mynat.

    Axiom _fake_one_mul : forall a : mynat, _fake_mul _fake_one a = a.
    Axiom _fake_zero_mul : forall a : mynat, _fake_mul 0 a = 0.
    Axiom _fake_mul_comm : forall (a b: mynat), _fake_mul a b = _fake_mul b a.
    Axiom _fake_mul_assoc : forall (a b c: mynat), _fake_mul a (_fake_mul b c) = _fake_mul (_fake_mul a b) c.
    Axiom _fake_distr_mul : forall (a b c : mynat), _fake_mul (a + b) c = (_fake_mul a c) + (_fake_mul b c).

    Lemma assoc_add (a b c : mynat) : a + (b + c) = (a + b) + c.
    Proof.
        rewrite add_assoc; easy.
    Qed.

    Definition mynat_semi_ring :=
        mk_srt 0 _fake_one add _fake_mul (@eq _) 
        zero_add add_comm assoc_add _fake_one_mul _fake_zero_mul _fake_mul_comm 
        _fake_mul_assoc _fake_distr_mul.

End SemiRingFaking.

Add Ring _fake_mynat_ring : SemiRingFaking.mynat_semi_ring.

Lemma test (a b c d e : mynat) : (((a+b)+c)+d)+e=(c+((b+e)+a))+d.
Proof.
    ring.
Qed.

Fixpoint mul (n m : mynat) : mynat :=
    match m with
    | O => O
    | S p => (mul n p) + n
    end.

Infix "*" := mul.
Notation "(*)" := mul (only parsing).
Notation "( f *)" := (mul f) (only parsing).
Notation "(* f )" := (fun g => mul g f) (only parsing).

Fact mul_zero (a : mynat) : a * 0 = 0.
Proof.
    trivial.
Qed.

Fact mul_succ (a b : mynat) : a * S b = a * b + a.
Proof.
    trivial.
Qed.

(* Level 0 data *)
(* name `zero_mul` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 0 prologue *)
(*
I have just defined multiplication for you. It is defined to satisfy the following
two statements:
<ul>
    <li>`Fact mul_zero (a : mynat) : a * 0 = 0.`</li>
    <li>`Fact mul_succ (a b : mynat) : a * S b = a * b + a.`</li>
</ul>
Basically, we have defined multiplication inductively on the second variable.

You can still use all your theorems from Addition World, even from levels you have
not completed yet! I do recommend you complete all of them before you continue,
just so you are familiar with them.

Anyway, just like for addition in the previous world, we know next to nothing 
about multiplication so let's start proving some lemmas! Remember that the
`induction` tactic will come in very useful, like in the previous world.
*)
Lemma zero_mul (m : mynat) : 0 * m = 0.
Proof.
    induction m as [| ? H].
    - rewrite mul_zero; easy.
    - rewrite mul_succ. easy.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name `mul_one` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 1 prologue *)
(*
Recall that you can find all the theorems we have shown before in the side
menu on the left. In this level in particular, we will need to use
```
#Fact one_eq_succ_zero : 1 = S 0.
```
Let's prove that `1` is actually the neutral element for multiplication
(at least on the right, since we don't know that multiplication is commutative yet)!
*)
Lemma mul_one (m : mynat) : m * 1 = m.
Proof.
    rewrite one_eq_succ_zero, mul_succ.
    rewrite mul_zero, zero_add.
    reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 *)
(* Level 2 data *)
(* name `one_mul` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 2 prologue *)
(*
Let's show that `1` is also a unit on the left. the following theorems
may be useful:
<ul>
    <li>`Fact one_eq_succ_zero : 1 = S 0.`</li>
    <li>`Fact succ_eq_add_one a : S a = a + 1`</li>
</ul>
*)
Lemma one_mul (m : mynat) : 1 * m = m.
Proof.
    induction m as [| ? H].
    - trivial.
    - rewrite mul_succ.
      now rewrite H.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 *)
(* Level 3 data *)
(* name `mul_add` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 3 prologue *)
(*
The goal for this world is to show `mul_comm` and `mul_assoc`,
i.e. that multiplication is commutative (`a * b = b * a`) and associative
(`(a * b) * c = a * (b * c)`). However, we also want to show
how multiplication interacts with addition. In this level
we show that multiplication is left distributive. Note that
the name of the lemma (`mul_add`) refers to the order in which
the operations are written here, and is not `mul_left_distrib`
or something like that, which would be much harder to remember!
*)
Lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b.
Proof.
    induction b as [| ? H].
    - easy.
    - rewrite add_succ.
      repeat rewrite mul_succ.
      rewrite H.
      ring.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 *)
(* Level 4 data *)
(* name `mul_assoc` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 4 prologue *)
(*
Alright, time to show that multiplication is associative!

By the way, did you know you could add the tactic `now` before
any tactic you type, and it will check if it can be easily
shown (for example by `reflexivity`) after performing the
tactic you write after it. So for example, you could write
```
now rewrite mul_add.
```
to perform a `rewrite mul_add`, and then check if the proof
can easily be finished. You can think of this as if it was
the same as
```
rewrite mul_add.
reflexivity.
``` 
for now. Try it out!
*)
Lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c).
Proof.
    induction c as [| ? H].
    - repeat rewrite mul_zero; easy.
    - repeat rewrite mul_succ.
      rewrite H.
      now rewrite mul_add.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 *)
(* Level 5 data *)
(* name `succ_mul` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 5 prologue *)
(* 
Another tactic that might come in useful is `f_equal`.
Basically, if your goal contains an equality of constructors,
i.e.
```
S (x + y + z) = S(x + z + y)
```
you can use the tactic `f_equal` to turn it into
```
x + y + z = x + z + y
```
It might come in useful for this level!
*)
Lemma succ_mul (a b : mynat) : (S a) * b = a * b + b.
Proof.
    induction b as [| ? H].
    - repeat rewrite mul_zero; easy.
    - repeat rewrite mul_succ.
      rewrite H.
      repeat rewrite add_succ.
      f_equal.
      ring.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 *)
(* Level 6 data *)
(* name `add_mul` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 6 prologue *)
(*
We already have `mul_add`, but we have not shown how multiplication
interacts on the right with addition. If you end up with a goal
that only contains addition, with some messy parentheses or different
orders of terms, try not to mess with `rewrite add_comm` and friends, 
but use the powerful `ring` tactic instead!
*)
Lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t.
Proof.
    induction t as [| ? H].
    - now repeat rewrite mul_zero.
    - repeat rewrite mul_succ.
      rewrite H.
      ring.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 7 *)
(* Level 7 data *)
(* name `mul_comm` (boss level!) *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 7 prologue *)
(*
The boss level for this world! You should be well prepared,
if you've done all the levels so far. 
*)
Lemma mul_comm (a b : mynat) : a * b = b * a.
Proof.
    induction b as [| ? H].
    - now rewrite mul_zero, zero_mul.
    - rewrite mul_succ, succ_mul.
      now rewrite H.
Qed.
(* Level epilogue *)
(*
Now we know that `mynat` is a commutative semiring! Just one
more level and we will be able to beef up our `ring` tactic!
*)
(* Level end *)

(* Level 8 *)
(* Level 8 data *)
(* name `mul_left_assoc` *)
(* tactics induction *)
(* theorems mul_succ *)
(* Level 8 prologue *)
(*
Equipped with
<ul>
    <li>`Lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c).`</li>
    <li>`Lemma mul_comm (a b : mynat) : a * b = b * a.`</li>
</ul>
this level should be a piece of cake!
*)
Lemma mul_left_assoc (a b c : mynat) : a * (b * c) = (a * b) * c.
Proof.
    rewrite <- mul_assoc.
    reflexivity.
Qed.
(* Level epilogue *)
(*
And now, after I invert `add_assoc` into 
```
#Lemma add_left_assoc (a b c : mynat) : a + (b + c) = (a + b) + c.
```
I can type
```
#Definition mynat_semi_ring : semi_ring_theory 0 1 add mul (@eq _).
#Proof.
#    constructor.
#    - exact zero_add.
#    - exact add_comm.
#    - exact add_left_assoc.
#    - exact one_mul.
#    - exact zero_mul.
#    - exact mul_comm.
#    - exact mul_left_assoc.
#    - exact add_mul.
#Qed.
#
#Add Ring mynat_ring : mynat_semi_ring.
```
and our `ring` tactic will now also solve basic
equations involving multiplications for us!

If you click "Next Level", you will be sent to Power World.
This world is optional, but can be seen as kind of a "Boss World",
involving the theorems we have shown in Addition and Multiplication World.

If you want to skip this world though, you can go back to the main menu to
go to Function World instead!
*)
(* Level end *)

Lemma add_left_assoc (a b c : mynat) : a + (b + c) = (a + b) + c.
Proof.
    rewrite <- add_assoc.
    reflexivity.
Qed.

Definition mynat_semi_ring : semi_ring_theory 0 1 add mul (@eq _).
Proof.
    constructor.
    - exact zero_add.
    - exact add_comm.
    - exact add_left_assoc.
    - exact one_mul.
    - exact zero_mul.
    - exact mul_comm.
    - exact mul_left_assoc.
    - exact add_mul.
Qed.

Add Ring mynat_ring : mynat_semi_ring.