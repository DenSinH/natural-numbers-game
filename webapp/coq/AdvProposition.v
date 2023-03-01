(* Level 0 data *)
(* name the `split` tactic *)
(* tactics induction *)
(* Level prologue *)
Example prop_and (P Q : Prop) (p : P) (q : Q) : P /\ Q.
Proof.
    split.
    - exact p.
    - exact q.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 1 data *)
(* name the `destruct` tactic *)
(* tactics induction *)
(* Level prologue *)
Lemma and_symm (P Q : Prop) : P /\ Q -> Q /\ P.
Proof.
    intro h.
    destruct h as [p q].
    split.
    - exact q.
    - exact p.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 2 data *)
(* name `and_trans` *)
(* tactics induction *)
(* Level prologue *)
Lemma and_trans (P Q R : Prop) : P /\ Q -> Q /\ R -> P /\ R.
Proof.
    intros h1 h2.
    destruct h1 as [p _].
    destruct h2 as [_ r].
    split.
    - exact p.
    - exact r.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 3 data *)
(* name `iff_trans` *)
(* tactics induction *)
(* Level prologue *)
Lemma iff_trans (P Q R : Prop) : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros h1 h2.
    destruct h1 as [pq qp].
    destruct h2 as [qr rq].
    split.
    - intro p. exact (qr (pq p)).
    - intro r. exact (qp (rq r)).
Qed.
(* Level epilogue *)
(* Level end *)

(* Lean has alternate notation to destruct (/case in lean) and a level for this *)
(* This is also interesting though *)
Require Import Setoid.

(* Level 4 data *)
(* name `iff_trans` easter eggs *)
(* tactics induction *)
(* Level prologue *)
Lemma iff_trans2 (P Q R : Prop) : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros h1 h2.
    rewrite h1, h2.
    reflexivity.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 5 data *)
(* name Or, and the `left` and `right` tactics *)
(* tactics induction *)
(* Level prologue *)
Example prop_or (P Q : Prop) : Q -> (P \/ Q).
Proof.
    intro q.
    right.
    exact q.
Qed.
(* Level epilogue *)
(* Level end *)

(* Level 6 data *)
(* name `or_symm` *)
(* tactics induction *)
(* Level prologue *)
Lemma or_symm (P Q : Prop) : (P \/ Q) -> (Q \/ P).
Proof.
    intro h.
    (* Performs case analysis on h *)
    destruct h as [p|q].
    - right; exact p.
    - left; exact q.
Qed.
(* Level epilogue *)
(* Level end *)


(* Level 7 data *)
(* name `and_or_distrib_left` *)
(* tactics induction *)
(* Level prologue *)
Lemma and_or_distrib_left (P Q R : Prop) : P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
    tauto.
Qed.
(* Level epilogue *)
(*
A proof using only basic tactics might be 
```
split.
- intro h.
  destruct h as [p qr].
  destruct qr as [q|r].
  * left; split.
    + exact p.
    + exact q.
  * right; split.
    + exact p.
    + exact r.
- intro h.
  destruct h as [pq|pr].
  * destruct pq as [p q].
    split.
    + exact p.
    + left; exact q.
  * destruct pr as [p r].
    split.
    + exact p.
    + right; exact r.
```
*)
(* Level end *)

(* Level 8 data *)
(* name `exfalso` and proof by contradiction *)
(* tactics induction *)
(* Level prologue *)
Lemma contra (P Q : Prop) : (P /\ ~P) -> Q.
Proof.
    tauto.
Qed.
(* Level epilogue *)
(* Level end *)

(* Adds law of excluded middle, this is not really very HoTT *)
Require Import Classical.

(* Level 9 data *)
(* name the law of the excluded middle *)
(* tactics induction *)
(* Level prologue *)
Lemma contrapositive (P Q : Prop) : (~Q -> ~P) -> (P -> Q).
Proof.
    unfold not.
    intros h p.
    destruct (classic Q) as [q|nq].
    - exact q.
    - apply False_ind.
      apply h.
      * exact nq.
      * exact p.
Qed.
(* Level epilogue *)
(* Level end *)

