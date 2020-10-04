theory Concrete_Semantics_2_5_ex10
imports Main
begin

datatype tree0 = Tip | Node "tree0" "tree0"

(* counts the number of all nodes (inner nodes and leaves) *)
fun nodes :: "tree0 => nat" where
"nodes Tip = 1" |
"nodes (Node a b) = 1 + nodes a + nodes b"

fun explode :: "nat => tree0 => tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

(* Find an equation expressing the size of a tree after exploding it *)
(* s : nodes of tree, then 
case 0: s
case 1: 2s + 1
case 2: 2(2s + 1) + 1
case 3: 2(4s + 3) + 1
case n: 2^n * s + 2^n - 1
 *)

lemma "nodes (explode n t) = (2 ^ n) * nodes t + (2 ^ n) - 1"
  apply(induction n arbitrary: t)
  apply(auto)
  apply(simp add:algebra_simps)
  done

end