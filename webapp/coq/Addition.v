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
(* tactics induction *)
(* theorems add_succ *)
(* Level 2 prologue *)
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
(* tactics induction *)
(* theorems add_succ *)
(* Level 3 prologue *)
Lemma add_comm (a b : mynat) : a + b = b + a.
Proof.
  induction b as [| ? H].
  - now rewrite add_zero, zero_add.
  - rewrite add_succ, succ_add.
    now rewrite H.
Qed.

(* Given in natural numbers game *)
Definition I := S 0.
Notation "1" := I.
Fact one_eq_succ_zero : 1 = S 0.
Proof.
  trivial.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 data *)
(* name `succ_eq_add_one` *)
(* tactics induction *)
(* theorems one_eq_succ_zero *)
(* Level 4 prologue *)
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
(* tactics induction *)
(* theorems one_eq_succ_zero *)
(* Level 5 prologue *)
Lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b.
Proof.
  rewrite add_assoc.
  rewrite (add_comm b c).
  (* Can just use the forward direction but whatever *)
  rewrite <- add_assoc.
  reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)
