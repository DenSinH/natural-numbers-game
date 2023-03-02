From NaturalNumbers Require Export Base Tutorial Addition.

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

Inductive _mexp : Set :=
    | Ident : _mexp
    | Var : mynat -> _mexp
    | Op: _mexp -> _mexp -> _mexp.

Fixpoint _mdenote (me : _mexp) : mynat :=
    match me with
        | Ident => 0
        | Var v => v
        | Op me1 me2 => _mdenote me1 + _mdenote me2
    end.

Require Import List.

Fixpoint _mldenote (ls : list mynat) : mynat :=
    match ls with
        | nil => 0
        | x :: ls' => x + _mldenote ls'
    end.

Fixpoint _flatten (me : _mexp) : list mynat :=
    match me with
        | Ident => nil
        | Var x => x :: nil
        | Op me1 me2 => _flatten me1 ++ _flatten me2
    end.

Lemma _flatten_correct' : forall ml2 ml1,
    _mldenote ml1 + _mldenote ml2 = _mldenote (ml1 ++ ml2).
    induction ml1 as [| a b H].
    - simpl. 
      rewrite zero_add. 
      reflexivity.
    - simpl.
      rewrite <- H. 
      rewrite add_assoc. 
      reflexivity.
Qed.

Theorem _flatten_correct : forall me, _mdenote me = _mldenote (_flatten me).
    Hint Resolve _flatten_correct'.

    induction me as [| |a Ha b Hb].
    - trivial.
    - trivial.
    - simpl.
      rewrite Ha, Hb.
      rewrite _flatten_correct'.
      reflexivity.
Qed.

Theorem monoid_reflect : forall me1 me2,
    _mldenote (_flatten me1) = _mldenote (_flatten me2)
    -> _mdenote me1 = _mdenote me2.
    intros; repeat rewrite _flatten_correct; assumption.
Qed.

Ltac reify me :=
    match me with
      | 0 => Ident
      | ?me1 + ?me2 =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          constr:(Op r1 r2)
      | _ => constr:(Var me)
    end.

Ltac monoid :=
    match goal with
        | [ |- ?me1 = ?me2 ] =>
        let r1 := reify me1 in
        let r2 := reify me2 in
            change (_mdenote r1 = _mdenote r2);
            apply monoid_reflect; simpl
    end.

Theorem t1 : forall a b c d, a + b + c + d = a + (b + c) + d.
Proof.
    intros. monoid.
    reflexivity.
Qed.

Lemma test (a b c d e : mynat) : (((a+b)+c)+d)+e=(c+((b+e)+a))+d.
Proof.
    intros. monoid.
    
Abort.


