From NaturalNumbers Require Export Base Tutorial Addition Multiplication AdvProposition.

Require Coq.Classes.RelationClasses.

Fact succ_inj {a b : mynat} : S a = S b -> a = b.
Proof.
    intro h.
    inversion h.
    reflexivity.
Qed.

Fact zero_ne_succ (a : mynat) : 0 <> S a.
Proof.
    discriminate.
Qed.

(* Level 0 data *)
(* name `succ_inj`. A function. *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma succ_inj' {a b : mynat} (hs : S a = S b) : a = b.
Proof.
    exact (succ_inj hs).
    (* apply succ_inj.
       exact hs. *)
    (* inversion hs.
       reflexivity. *)
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name `succ_succ_inj` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma succ_succ_inj {a b : mynat} (h : S (S a) = S (S b)) : a = b.
Proof.
    exact (succ_inj (succ_inj h)).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name `succ_eq_succ_of_eq` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma succ_eq_succ_of_eq {a b : mynat} : a = b -> S a = S b.
Proof.
    intro h.
    now rewrite h.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `eq_iff_succ_eq_succ` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma eq_iff_succ_eq_succ (a b : mynat) : S a = S b <-> a = b.
Proof.
    split.
    - exact succ_inj.
    - exact succ_eq_succ_of_eq.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 4 data *)
(* name `add_right_cancel` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma add_right_cancel (a b t : mynat) : a + t = b + t -> a = b.
Proof.
    intro h.
    induction t as [| ? Ht].
    - rewrite add_zero in h.
      exact h.
    - repeat rewrite add_succ in h.
      inversion h.
      exact (Ht H0).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name `add_left_cancel` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma add_left_cancel (t a b : mynat) : t + a = t + b -> a = b.
Proof.
    rewrite add_comm, (add_comm t b).
    exact (add_right_cancel _ _ _ ).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `add_right_cancel_iff` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma add_right_cancel_iff (t a b : mynat) : a + t = b + t <-> a = b.
Proof.
    split.
    - exact (add_right_cancel _ _ _).
    - intro h.
      now rewrite h.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 7 data *)
(* name `eq_zero_of_add_right_eq_self` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a -> b = 0.
Proof.
    intro h.
    specialize (add_left_cancel a b 0) as h_simpl.
    rewrite (add_zero a) in h_simpl.
    exact (h_simpl h).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 8 data *)
(* name `succ_ne_zero` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma succ_ne_zero (a : mynat) : S a <> 0.
Proof.
    (* todo: symmetry for <>? *)
    discriminate.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 9 data *)
(* name `add_left_eq_zero` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma add_left_eq_zero {a b : mynat} (h : a + b = 0) : b = 0.
Proof.
    destruct b.
    - reflexivity.
    - exfalso.
      rewrite add_succ in h.
      specialize (succ_ne_zero (a + b)) as snz.
      unfold not in snz.
      exact (snz h).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 10 data *)
(* name `add_right_eq_zero` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma add_right_eq_zero {a b : mynat} : a + b = 0 -> a = 0.
Proof.
    rewrite add_comm.
    apply add_left_eq_zero.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 11 data *)
(* name `add_one_eq_succ` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma add_one_eq_succ (d : mynat) : d + 1 = S d.
Proof.
    symmetry.
    exact (succ_eq_add_one _).
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 12 data *)
(* name `ne_succ_self` *)
(* tactics induction *)
(* theorems zero_ne_succ *)
(* Level prologue *)
Lemma ne_succ_self (n : mynat) : n <> S n.
Proof.
    unfold not.
    induction n as [| ? h].
    - easy.
    - intro h1.
      now specialize (succ_inj h1) as h2.
Qed.
(* Level epilogue *)
(* Level end *)