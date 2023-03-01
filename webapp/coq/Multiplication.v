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

(* Level 0 *)
Lemma zero_mul (m : mynat) : 0 * m = 0.
Proof.
    induction m as [| ? H].
    - rewrite mul_zero; easy.
    - rewrite mul_succ. easy.
Qed.

(* Level 1 *)
Lemma mul_one (m : mynat) : m * 1 = m.
Proof.
    rewrite one_eq_succ_zero, mul_succ.
    rewrite mul_zero, zero_add.
    reflexivity.
Qed.

(* Level 2 *)
Lemma one_mul (m : mynat) : 1 * m = m.
Proof.
    induction m as [| ? H].
    - trivial.
    - rewrite mul_succ.
      now rewrite H.
Qed.

(* Level 3 *)
Lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b.
Proof.
    induction b as [| ? H].
    - easy.
    - rewrite add_succ.
      repeat rewrite mul_succ.
      rewrite H.
      ring.
Qed.

(* Level 4 *)
Lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c).
Proof.
    induction c as [| ? H].
    - repeat rewrite mul_zero; easy.
    - repeat rewrite mul_succ.
      rewrite H.
      now rewrite mul_add.
Qed.

(* Level 5 *)
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

(* Level 6 *)
Lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t.
Proof.
    induction t as [| ? H].
    - now repeat rewrite mul_zero.
    - repeat rewrite mul_succ.
      rewrite H.
      ring.
Qed.

(* Level 7 *)
Lemma mul_comm (a b : mynat) : a * b = b * a.
Proof.
    induction b as [| ? H].
    - now rewrite mul_zero, zero_mul.
    - rewrite mul_succ, succ_mul.
      now rewrite H.
Qed.

(* Level 8 *)
Lemma mul_left_assoc (a b c : mynat) : a * (b * c) = (a * b) * c.
Proof.
    rewrite <- mul_assoc.
    reflexivity.
Qed.

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