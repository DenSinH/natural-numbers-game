(* Level 0 *)
Example prop_and (P Q : Prop) (p : P) (q : Q) : P /\ Q.
Proof.
    split.
    - exact p.
    - exact q.
Qed.

(* Level 1 *)
Lemma and_symm (P Q : Prop) : P /\ Q -> Q /\ P.
Proof.
    intro h.
    destruct h as [p q].
    split.
    - exact q.
    - exact p.
Qed.

(* Level 2 *)
Lemma and_trans (P Q R : Prop) : P /\ Q -> Q /\ R -> P /\ R.
Proof.
    intros h1 h2.
    destruct h1 as [p _].
    destruct h2 as [_ r].
    split.
    - exact p.
    - exact r.
Qed.

(* Level 3 *)
Lemma iff_trans (P Q R : Prop) : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros h1 h2.
    destruct h1 as [pq qp].
    destruct h2 as [qr rq].
    split.
    - intro p. exact (qr (pq p)).
    - intro r. exact (qp (rq r)).
Qed.

(* Lean has alternate notation to destruct (/case in lean) and a level for this *)
(* This is also interesting though *)
Require Import Setoid.

(* Level 4 *)
Lemma iff_trans2 (P Q R : Prop) : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros h1 h2.
    rewrite h1, h2.
    reflexivity.
Qed.

(* Level 5 *)
Example prop_or (P Q : Prop) : Q -> (P \/ Q).
Proof.
    intro q.
    right.
    exact q.
Qed.

(* Level 6 *)
Lemma or_symm (P Q : Prop) : (P \/ Q) -> (Q \/ P).
Proof.
    intro h.
    (* Performs case analysis on h *)
    destruct h as [p|q].
    - right; exact p.
    - left; exact q.
Qed.


(* Level 7 *)
Lemma and_or_distrib_left (P Q R : Prop) : P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
    tauto.
    (*
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
    *)
Qed.

(* Level 8 *)
Lemma contra (P Q : Prop) : (P /\ ~P) -> Q.
Proof.
    tauto.
Qed.

Theorem easy : forall p q:Prop, (p->q)->(~q->~p).
Proof. 
intros. 
intro. 
apply H0. 
apply H. 
exact H1. 
Qed.

(* Adds law of excluded middle, this is not really very HoTT *)
Require Import Classical.

(* Level 9 *)
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

