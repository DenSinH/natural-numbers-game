
(* Level 0 data *)
(* name the `exact` tactic *)
(* tactics apply *)
(* available false *)
(* Level prologue *)
(*
Classically, you can think of a proposition to be a statement
that is True or False. In Homotopy Type Theory, this definition
is a bit more subtle, but instead of `Type`s we may use
`Prop`s. You can think of types `P : Prop` as propositions, and
elements `p : P` as proofs for the proposition `P`. In this case,
functions `P -> Q` become like implications, where we wish to produce
a proof of the proposition `Q` from a proof `p : P` of 
the proposition `P`. 

Remember our `exact` tactic. It works the same here as in the previous
world, so the proof of this lemma may seem familiar. If you forgot how
you proved this statement for `Type`s in Function World, feel free
to go back and look at your proof there!
*)
Example level0 (P Q : Prop) (p : P) (h : P -> Q) : Q.
Proof.
    exact (h p).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name the `intro` tactic *)
(* tactics apply *)
(* available false *)
(* Level 1 prologue *)
(*
Let's prove an implication. Like I said in the previous level,
they are kind of like functions, except on `Prop`ositions instead of
`Type`s. In the below lemma,
typing `intro p` will kind of be like saying "assume `P` holds".
It then remains to present some element of type `P`. But we have a proof
of `P`, namely `p`, which we introduced before. It should be enough to then
type `exact p`.

Try it out below!
*)
Lemma imp_self (P : Prop) : P -> P.
Proof.
    intro p.
    exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name the `specialize` tactic *)
(* tactics apply *)
(* available false *)
(* Level 2 prologue *)
(*
Like in function world, we can still use the `specialize` tactic
to make it easier to later `exact _` something of the right type.
Indeed, here we could type 
```
exact (l(j(h(p))))
```
but you should try to use the `specialize` tactic to practice!
Remember, it should look something like
```
specialize (h p) as q.
```
*)
Lemma maze (P Q R S T U: Prop)
    (p : P)
    (h : P -> Q)
    (i : Q -> R)
    (j : Q -> T)
    (k : S -> T)
    (l : T -> U)
    : U.
Proof.
    remember (h p) as q.
    remember (j q : T) as t.
    (* what does eremember do vs remember? *)
    eremember (l(t)) as u.
    exact u.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name the `apply` tactic *)
(* tactics apply *)
(* available false *)
(* Level 3 prologue *)
(*
Our hypotheses kind of became a mess on the previous level, so 
we should try it again, but then using `apply`. Again, like in 
Function world, this allows us to "reason backwards". Try
to `apply` the right functions to turn our goal into `P`,
so we can `exact p.` to finish it off.
*)
Lemma maze2 (P Q R S T U: Prop)
    (p : P)
    (h : P -> Q)
    (i : Q -> R)
    (j : Q -> T)
    (k : S -> T)
    (l : T -> U)
    : U.
Proof.
    apply l.
    apply j, h.
    exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 data *)
(* name `P -> (Q -> P)` *)
(* tactics apply *)
(* available false *)
(* Level 4 prologue *)
(*
We want to show that `P -> (Q -> P)` where `P` and `Q` are propositions.
Think about our rule of thumb regarding functions/implications
and the `intro` tactic, and take a good look at our hypothesis
to see what we can `exact` or `apply` here. 

Remember you can also use the `intros` tactic to repeatedly 
introduce hypotheses?
*)
Example level4 (P Q : Prop) : P -> (Q -> P).
Proof.
    intros p q.
    exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name `(P -> (Q -> R)) -> ((P -> Q) -> (P -> R))` *)
(* tactics apply *)
(* available false *)
(* Level 5 prologue *)
(*
You can solve this level completely with `intro`, `apply` and `exact`.
However, it may happen that `apply`ing a function of type `P -> Q -> R`
produces two subgoals. If you're proving it this way, remember to use
dashes (these: `-`) to specifiy that you're working in a subgoal!
*)
Example level5 (P Q R : Prop) : (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
    intros j f p.
    apply j.
    - exact p.
    - exact (f p).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `(P -> Q) -> ((Q -> R) -> (P -> R))` *)
(* tactics apply *)
(* available false *)
(* Level 6 prologue *)
(*
In Function World, this level did not really mean much, but
thinking of `->` as implication, this level really shows
the transitivity of implications!
*)
Lemma imp_trans (P Q R : Type) : (P -> Q) -> ((Q -> R) -> (P -> R)).
Proof.
    intros f g h.
    apply g, f.
    exact h.
Qed.
(* Level epilogue *)
(* Level end *)

Lemma not_iff_impl_false (P : Prop) : ~ P <-> (P -> False).
Proof.
    unfold not.
    split.
    - trivial.
    - trivial.
Qed.

Require Setoid.

(* Level 7 data *)
(* name `(P -> Q) -> (~Q -> ~P)` *)
(* tactics unfold *)
(* available false *)
(* Level 7 prologue *)
(*
There is a `False` `Prop`osition, with no proofs (kind of 
like the empty type, with no inhabitants). We can use this
to define "negation" of a proposition (i.e. `~Q`). In reality,
we have that `~Q` is the same as `Q -> False`. 

I have added a lemma 
```
#Lemma not_iff_impl_false (P : Prop) : ~ P <-> (P -> False).
```
for you to use in this level. Use it to 
```
repeat rewrite not_iff_impl_false.
```
in this level to get rid of the `~`.

Later on, it might be easier to use Coq's own way of doing
this, by writing
```unfold not```
which basically `unfold`s the definition of `not` 
(the `~` operator). 

Try either of these ways in the proof below!
*)
Lemma contrapositive (P Q : Prop) : (P -> Q) -> (~Q -> ~P).
Proof.
    (* requires Setoid *)
    repeat rewrite not_iff_impl_false.
    intros f g p.
    exact (g (f p)).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 8 data *)
(* name a big maze *)
(* tactics unfold *)
(* available false *)
(* Level 8 prologue *)
(*
Try to solve the maze below using the tactics you have
learnt in Proposition World and Function World!
*)
Example level8 (A B C D E F G H I J K L : Prop)
    (f1 : A -> B) (f2 : B -> E) (f3 : E -> D) (f4 : D -> A) (f5 : E -> F)
    (f6 : F -> C) (f7 : B -> C) (f8 : F -> G) (f9 : G -> J) (f10 : I -> J)
    (f11 : J -> I) (f12 : I -> H) (f13 : E -> H) (f14 : H -> K) (f15 : I -> L)
: A -> L.
Proof.
    intro a.
    now apply f15, f11, f9, f8, f5, f2, f1.
Qed.
(* Level epilogue *)
(* Level end *)


