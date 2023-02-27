From NaturalNumbers Require Import Base Tutorial Addition.

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

Add Ring mynat_ring : SemiRingFaking.mynat_semi_ring.
Ltac _simpl := ring_simplify.

Lemma test (a b c d e : mynat) : (((a+b)+c)+d)+e=(c+((b+e)+a))+d.
Proof.
    _simpl.
    reflexivity.
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

(* Level 1 *)
Lemma zero_mul (m : mynat) : 0 * m = 0.
Proof.
    induction m as [| ? H].
    - rewrite mul_zero; easy.
    - rewrite mul_succ. easy.
Qed.

(* Level 2 *)
Lemma mul_one (m : mynat) : m * 1 = m.
Proof.
    rewrite one_eq_succ_zero, mul_succ.
    rewrite mul_zero, zero_add.
    reflexivity.
Qed.

(* Level 3 *)
Lemma one_mul (m : mynat) : 1 * m = m.
Proof.
    induction m as [| ? H].
    - trivial.
    - rewrite mul_succ.
      now rewrite H.
Qed.

(* Level 4 *)
Lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b.
Proof.
    induction b as [| ? H].
    - easy.
    - rewrite add_succ.
      repeat rewrite mul_succ.
      rewrite H, add_assoc. (* Would want to do _simpl here... *)
      reflexivity.
Qed.


(* Level 5 *)