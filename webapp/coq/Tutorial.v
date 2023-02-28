From NaturalNumbers Require Export Base.

(* Level 0 data *)
(* name The `reflexivity` tactic *)
(* tactics reflexivity *)
(* theorems null *)
(* available false *)
(* Level 0 prologue *)
(* 
This is some information about level 0. I want to write a lot of text 
here to explain what is going on in coq etc. I will also write some
`code` that should be formated, perhaps even some more text blabla.

A new paragraph that should be rendered properly. Haha this is more text.
So interesting all this information. 

Lorem ipsum dolor sit amet, consectetuer adipiscing elit. 
Nunc vitae pede in erat dignissim accumsan. Etiam dolor.
Nam sapien. Curabitur ornare sem in mauris. In justo. 
In est diam, pretium in, faucibus sit amet, faucibus vel, urna. 
Ut eu justo quis enim nonummy fringilla. Phasellus luctus malesuada dolor. 
Sed molestie nulla in tortor. Proin non est. Curabitur dui ligula, 
tristique et, pharetra non, feugiat id, lectus. Mauris fringilla.
Nulla facilisi. Donec orci ipsum, bibendum ac, scelerisque quis, 
tristique sit amet, nisl.

Ut vel nunc id lorem faucibus feugiat. 
Etiam commodo sem sed augue. Sed elementum.
Quisque turpis dui, rutrum quis, vehicula in, 
fringilla vel, lacus. Aliquam aliquam quam ac eros. 
Aliquam erat felis, aliquet vel, varius vel, ornare et, ante.
Curabitur condimentum sollicitudin ipsum. Donec sed leo sit amet
felis laoreet vestibulum. Duis sed sem. Duis nibh urna, faucibus 
id, nonummy sit amet, nonummy ut, velit. Donec in wisi. Etiam 
pretium porta enim. Phasellus ac ligula eu orci iaculis tincidunt.
Integer sem. Sed rhoncus. Fusce diam arcu, faucibus ut, dapibus a, 
pulvinar et, leo. Duis dignissim erat sit amet dolor.

Vestibulum id mauris id augue pulvinar vehicula. Donec diam neque,
laoreet non, eleifend et, lobortis eu, leo. Donec sit amet magna.
Curabitur tortor sapien, mollis ac, accumsan non, ullamcorper at,
ligula. Nam ut velit sit amet massa cursus accumsan. Nullam neque
est, elementum vel, condimentum at, lobortis non, quam. Ut
posuere. Mauris et neque quis eros porttitor dictum. Nulla mi 
magna, semper a, nonummy et, varius quis, urna. Sed tincidunt,
risus sed imperdiet aliquam, nisl justo ornare ante, a egestas 
nibh felis non turpis. Sed euismod. Aliquam erat volutpat. 
Praesent at sem. Mauris mauris pede, laoreet id, aliquet semper, 
molestie eget, wisi. Sed non tellus. In auctor felis semper nibh.
Ut auctor. Suspendisse nibh. Curabitur et lorem. Praesent pede. 
Ut euismod nunc id mi. In ante nulla, egestas quis, pharetra et, 
egestas at, wisi. Phasellus massa.
*)
(* Level 0 lemma *)
Example refl (x : mynat) : x = x.
(* Level 0 proof *)
Proof.
    reflexivity.
Qed.
(* Level 0 epilogue *)
(*
Lorem ipsum dolor sit amet, consectetuer adipiscing elit. 
Nunc vitae pede in erat dignissim accumsan. Etiam dolor.
Nam sapien. Curabitur ornare sem in mauris. In justo. 
In est diam, pretium in, faucibus sit amet, faucibus vel, urna. 
Ut eu justo quis enim nonummy fringilla. Phasellus luctus malesuada dolor. 
Sed molestie nulla in tortor. Proin non est. Curabitur dui ligula, 
tristique et, pharetra non, feugiat id, lectus. Mauris fringilla.
Nulla facilisi. Donec orci ipsum, bibendum ac, scelerisque quis, 
tristique sit amet, nisl.

Ut vel nunc id lorem faucibus feugiat. 
Etiam commodo sem sed augue. Sed elementum.
Quisque turpis dui, rutrum quis, vehicula in, 
fringilla vel, lacus. Aliquam aliquam quam ac eros. 
Aliquam erat felis, aliquet vel, varius vel, ornare et, ante.
Curabitur condimentum sollicitudin ipsum. Donec sed leo sit amet
felis laoreet vestibulum. Duis sed sem. Duis nibh urna, faucibus 
id, nonummy sit amet, nonummy ut, velit. Donec in wisi. Etiam 
pretium porta enim. Phasellus ac ligula eu orci iaculis tincidunt.
Integer sem. Sed rhoncus. Fusce diam arcu, faucibus ut, dapibus a, 
pulvinar et, leo. Duis dignissim erat sit amet dolor.

Vestibulum id mauris id augue pulvinar vehicula. Donec diam neque,
laoreet non, eleifend et, lobortis eu, leo. Donec sit amet magna.
Curabitur tortor sapien, mollis ac, accumsan non, ullamcorper at,
ligula. Nam ut velit sit amet massa cursus accumsan. Nullam neque
est, elementum vel, condimentum at, lobortis non, quam. Ut
posuere. Mauris et neque quis eros porttitor dictum. Nulla mi 
magna, semper a, nonummy et, varius quis, urna. Sed tincidunt,
risus sed imperdiet aliquam, nisl justo ornare ante, a egestas 
nibh felis non turpis. Sed euismod. Aliquam erat volutpat. 
Praesent at sem. Mauris mauris pede, laoreet id, aliquet semper, 
molestie eget, wisi. Sed non tellus. In auctor felis semper nibh.
Ut auctor. Suspendisse nibh. Curabitur et lorem. Praesent pede. 
Ut euismod nunc id mi. In ante nulla, egestas quis, pharetra et, 
egestas at, wisi. Phasellus massa.
*)
(* Level 0 end *)


(* Level 1 data *)
(* name The `rewrite` tactic *)
(* tactics rewrite *)
(* theorems null *)
(* available false *)
(* Level 1 prologue *)
(* Level 1 lemma *)
Example rewr (x y z : mynat) (h : x = y + z) : x + z = y + z + z.
(* Level 1 proof *)
Proof.
    rewrite h.
    reflexivity.
Qed.
(* Level 1 epilogue *)
(* Level 1 end *)


(* Level 2 data *)
(* name The `rewrite` tactic *)
(* tactics rewrite *)
(* theorems null *)
(* available false *)
(* Level 2 prologue *)
(* Level 2 lemma *)
Example peano (a b : mynat) (h : S a = b) : S a = b.
(* Level 2 proof *)
Proof.
    rewrite <- h.
    reflexivity.
Qed.
(* Level 2 epilogue *)
(* Level 2 end *)

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

(* Level 3 data *)
(* name The `rewrite` tactic *)
(* tactics rewrite *)
(* theorems add_succ *)
(* available false *)
(* Level 3 prologue *)
(* Level 3 lemma *)
Lemma add_succ_zero (a : mynat) : a + S 0 = S a.
(* Level 3 proof *)
Proof.
    rewrite add_succ.
    rewrite add_zero.
    reflexivity.
Qed.
(* Level 3 epilogue *)
(* Level 3 end *)