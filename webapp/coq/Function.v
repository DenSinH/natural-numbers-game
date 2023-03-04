From NaturalNumbers Require Export Base Tutorial Addition Multiplication Power.

(* Level 0 data *)
(* name the `exact` tactic *)
(* tactics exact *)
(* available false *)
(* Level 0 prologue *)
(*
We have learnt a few tactics to manipulate expressions,
but those will not be of much to manipulate the main object
of this world: functions! To manipulate functions, we need
to learn about the tactics `exact`, `intro` and `apply`. 

Ultimately, we will use these things to show theorems about
`mynat`, but it is not necessary to use this specific type,
as the statements about functions will hold on any type!

In this world, we will use capital letters (`P`, `Q`, `R`)
to denote types, and lowercase letters `h`, `j`, `k` for
functions between them.

<h3>A new kind of goal</h3>

So far, we have only seen goals in the form of equations,
but a goal can also be a type, where we wish to find an 
instance of a certain type. You may have already seen that the
goal for this level looks like
```plaintext
  P : Type
  Q : Type
  p : P
  h : P -> Q
  ============================
  Q
```
and the point is that we wish to find some element of type `Q`.

<h3>The `exact` tactic</h3>

If we can construct an element of the goal type from our assumptions,
we can use the `exact` tactic to finish the goal. For example,
if we have the context like the one above, we could obtain
an element of type `Q`, namely `h(p)`. We write 
```
exact (h p).
``` 
to close the goal. Try it out!
*)
Example level0 (P Q : Type) (p : P) (h : P -> Q) : Q.
Proof.
    exact (h p).
Qed.
(* Level epilogue *)
(* Level end *)

Definition III := S II.
Notation "3" := III.

(* Level 1 data *)
(* name the `intro` tactic *)
(* tactics intro *)
(* available false *)
(* Level 1 prologue *)
(*
The goal might also be a function type. In this level,
it is a function `mynat -> mynat`. In order to define
a function, we need to know what it does to every element.

In order to define a function in this way in our proof, 
we use the `intro` tactic. Suppose we have `X Y : Type`, and
the goal is of type `X -> Y`. We could type `intro x`, and
we get an `x : X` in our assumptions, and the goal will transform
to giving an element of `Y`. 

As a rule of thumb: if the goal is a function type (with `->`),
typing `intro p` will help.

For example in this lemma, try to define a function that sends `n : mynat`
to `3 * n + 2` (don't worry, I have defined `3` for you!). Do this by
typing `intro n.`, to give us an `n : mynat` in the assumptions, and then
typing `exact (3 * n + 2).` to present a constructed element of `mynat`.

Try it out!
*)
Example level1 : mynat -> mynat.
Proof.
    intro n.
    exact (3 * n + 2).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name the `specialize` tactic *)
(* tactics specialize *)
(* available false *)
(* Level 2 prologue *)
(*
We might have a whole lot of functions, like in the diagram below:
```plaintext
        h       i
p : P ----> Q ----> R
            |
            |j
            |
        k   v   l
    S ----> T ----> U
```
and so it might be cumbersome and a bit unreadable to type
```
exact (l(j(h(p)))).
```
in a single expression. To make this easier,
we use the `specialize` tactic. We can type
```
specialize (h p) as q.
```
to construct `q : Q` and add it to our assumptions, so
we can use it in further expressions. For example, we can
then use it to construct
```
specialize (j q : T) as t.
```
where we explicitly say that it is in `T` (which is kind of unnecessary,
but possible if you want!).

Remember to use the `exact` tactic once you have constructed an element
of type `U` below!
*)
Example level2 (P Q R S T U : Type)
    (p : P)
    (h : P -> Q)
    (i : Q -> R)
    (j : Q -> T)
    (k : S -> T)
    (l : T -> U)
    : U.
Proof.
    specialize (h p) as q.
    specialize (j q : T) as t.
    specialize (l(t)) as u.
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
Let's try this again, but in a different way. We have the same diagram
```plaintext
        h       i
p : P ----> Q ----> R
            |
            |j
            |
        k   v   l
    S ----> T ----> U
```
but now, instead of using `specialize`, which gives us a very long
list of hypothesis anyway, we use the `apply` tactic. Basically, this 
allows us to "reason backwards". If the goal is to construct an element
of type `U`, typing
```
apply l.
```
tells us that this would be the same as constructing an element of `T`, 
as we would be able to apply `l` to this element to obtain an element
of type `U`. Notice how the goal changes from `U` to `T` by typing this
tactic. 

Try to keep `apply`ing functions to turn the goal into `P`, so we can
simply `exact p` to finish the proof.
*)
Example level3 (P Q R S T U : Type)
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
In this level, we want to construct a function `P -> (Q -> P)`.

Let's think about how to proceed. Our rule of thumb tells us we
want to construct a function, so we should probably type `intro p`
to get `p : P` in our assumptions, and turn our goal into `Q -> P`.

Can you already tell what to do next? That's right, follow our rule of
thumb again, and typing `intro q` to obtain `q : Q` and transform
our goal into `P`. Now we can simply `exact p` to finish our proof.

<h3>The `intros` tactic</h3>

Instead of individually introducing `p` and `q`, you could also type
```
intros p q.
```
to do them both in one line!

Try it yourself!
*)
Example level4 (P Q : Type) : P -> (Q -> P).
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
Example level5 (P Q R : Type) : (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
    intros j f p.
    apply j.
    - exact p.
    - exact (f p).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `(P -> Q) -> ((Q -> F) -> (P -> F))` *)
(* tactics apply *)
(* available false *)
(* Level 6 prologue *)
(*
Notice that we are not really getting any useful theorems...
They don't even show up in the theorem window on the left. 
Oh well, it is useful practice, try to solve this one!
*)
Example level6 (P Q F : Type) : (P -> Q) -> ((Q -> F) -> (P -> F)).
Proof.
    intros f g h.
    apply g, f.
    exact h.
Qed.
(* Level epilogue *)
(* Level end *)

Require Import Init.Datatypes.

(* todo: unimath empty type / actual empty type? *)
Definition empty := Empty_set.

(* Level 7 data *)
(* name `(P -> Q) -> ((Q -> empty) -> (P -> empty))` *)
(* tactics apply *)
(* available false *)
(* Level 7 prologue *)
(*
In this level, we have replaced `F` with `empty`, the empty type.
Your goal might end up being to construct an element of the empty type!
Of course this is only possible because your assumptions might hold
some function to the empty type as well.
This may seem <i>contradictory</i>, but it all checks out!

Try it out, it should be similar to the previous level.
*)
Example level7 (P Q : Type) : (P -> Q) -> ((Q -> empty) -> (P -> empty)).
Proof.
    intros f g h.
    apply g, f.
    exact h.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 8 data *)
(* name a big maze (boss level!)*)
(* tactics apply *)
(* available false *)
(* Level 8 prologue *)
(*
Just to finish it all off, I give you a big maze to solve.
You can of course do it forwards and backwards, or both at the
same time. If you want, you can even draw a diagram to visualize
what is going on.
*)
Example level8 (A B C D E F G H I J K L : Type)
    (f1 : A -> B) (f2 : B -> E) (f3 : E -> D) (f4 : D -> A) (f5 : E -> F)
    (f6 : F -> C) (f7 : B -> C) (f8 : F -> G) (f9 : G -> J) (f10 : I -> J)
    (f11 : J -> I) (f12 : I -> H) (f13 : E -> H) (f14 : H -> K) (f15 : I -> L)
 : A -> L.
Proof.
    intro a.
    now apply f15, f11, f9, f8, f5, f2, f1.
Qed.
(* Level epilogue *)
(*
Off to Proposition World! The levels there may seem
a bit familiar to you if you have done all the levels in this world...
*)
(* Level end *)
