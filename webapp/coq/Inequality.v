From NaturalNumbers Require Import Base Tutorial Addition 
    Multiplication Power AdvAddition AdvMultiplication.

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

(* Level 0 *)
Lemma one_add_le_self (x : mynat) : x <= 1 + x.
Proof.
    exists 1.
    ring.
Qed.

(* Level 1 *)
Lemma le_refl (x : mynat) : x <= x.
Proof.
    exists 0.
    ring.
Qed.

Require Import Coq.Classes.RelationClasses.

Global Instance le_Reflexive : Reflexive le := le_refl.

Example refl : 0 <= 0.
Proof.
    reflexivity.
Qed.

(* Level 2 *)
Lemma le_succ (a b : mynat) : a <= b -> a <= S b.
Proof.
    intro h.
    destruct h as [c H].
    exists (S c).
    now rewrite H, add_succ.
Qed.

(* Level 3 *)
Lemma zero_le (a : mynat) : 0 <= a.
Proof.
    exists a.
    ring.
Qed.

(* Level 4 *)
Lemma le_trans (a b c : mynat) (hab : a <= b) (hbc : b <= c) : a <= c.
Proof.
    destruct hab as [ca ha].
    destruct hbc as [cb hb].
    rewrite ha in hb.
    exists (ca + cb).
    rewrite hb.
    ring.
Qed.

Global Instance le_Transitive : Transitive le := le_trans.
Global Instance le_PreOrder : PreOrder le.
Proof.
    constructor.
    - exact le_Reflexive.
    - exact le_Transitive.
Qed.

(* Level 5 *)
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


About PartialOrder.

Global Instance le_Antisymmetric : Antisymmetric _ _ le := le_antisymm.
Global Instance le_PartialOrder : PartialOrder _ le.
Proof.
    constructor.
    - intro h.
      split.
      * now exists 0.
      * now exists 0.
    - intro h.
      destruct h as [h1 h2].
      exact ((le_antisymm x x0) h1 h2).
Qed.

(* Level 6 *)
Lemma le_zero (a : mynat) (h : a <= 0) : a = 0.
Proof.
    destruct h as [c h].
    symmetry in h.
    exact (add_right_eq_zero h).
Qed.

(* Level 7 *)
Lemma succ_le_succ (a b : mynat) (h : a <= b) : S a <= S b.
Proof.
    destruct h as [c h].
    exists c.
    now rewrite h, succ_add.
Qed.

(* Level 8 *)
Lemma le_total (a b : mynat) : a <= b \/ b <= a.
Proof.
    revert a.
    induction b as[| ? h].
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

(* Total order? *)

(* Level 9 *)
(* "Two-line proof" *)
Lemma le_succ_self (a : mynat) : a <= S a.
Proof.
    rewrite succ_eq_add_one.
    now exists 1.
Qed.

(* Level 10 *)
Lemma add_le_add_right {a b : mynat} : a <= b -> forall (t : mynat), (a + t) <= (b + t).
Proof.
    intros h t.
    induction t as [| ? ht].
    - now simpl.
    - repeat rewrite add_succ.
      now apply succ_le_succ.
Qed.

(* Level 11 *)
Lemma le_of_succ_le_succ (a b : mynat) : S a <= S b -> a <= b.
Proof.
    intro h.
    destruct h as [c hc].
    rewrite succ_add in hc.
    exists c.
    now rewrite eq_iff_succ_eq_succ in hc.

    (* now inversion hc. *)
Qed.

(* Level 12 *)
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

(* Level 13 *)
Lemma add_le_add_left {a b : mynat} (h : a <= b) (t : mynat) : t + a <= t + b.
Proof.
    rewrite add_comm, (add_comm t b).
    exact (add_le_add_right h _).
Qed.

Definition lt (a b : mynat) := (a <= b) /\ ~(b <= a).

Infix "<" := lt.
Notation "(<)" := le (only parsing).
Notation "( f <)" := (le f) (only parsing).
Notation "(< f )" := (fun g => le g f) (only parsing).

(* Level 14 *)
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

(* Level 15 *)
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

(* Level 16 *)
Lemma lt_iff_succ_le (a b : mynat) : a < b <-> (S a) <= b.
Proof.
    split.
    - exact (lt_aux_one _ _).
    - exact (lt_aux_two _ _).
Qed.
