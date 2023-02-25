From NaturalNumbers Require Export Base.

(* Level 0 Start *)
Example refl (x : mynat) : x = x.
(* Level 0 Proof *)
Proof.
    reflexivity.
Qed.
(* Level 0 End *)

(* Level 1 Start *)
Example rewr (x y z : mynat) (h : x = y + z) : x + z = y + z + z.
(* Level 1 Proof *)
Proof.
    rewrite h.
    reflexivity.
Qed.
(* Level 1 End *)

(* Level 2 Start *)
Example peano (a b : mynat) (h : S a = b) : S a = b.
(* Level 2 Proof *)
Proof.
    rewrite <- h.
    reflexivity.
Qed.
(* Level 2 End *)

(* Given statements in Natural Numbers Game in Lean.
   They just write that Peano gave these.
   If we really wanted we could have just Admitted. them *)
Fact add_zero (n : mynat) : n + O = n.
Proof.
    induction n as [| ? H].
    - trivial.
    - simpl.
        rewrite H.
        reflexivity.
Qed.

Fact add_succ (m n : mynat) : n + (S m) = S (n + m).
Proof.
    induction n as [| ? H].
    - simpl.
        reflexivity.
    - simpl.
        rewrite H.
        reflexivity.
Qed.

(* Level 3 Start *)
Lemma add_succ_zero (a : mynat) : a + S O = S a.
(* Level 3 Proof *)
Proof.
    rewrite add_succ.
    rewrite add_zero.
    reflexivity.
Qed.
(* Level 3 End *)