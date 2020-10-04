theory Concrete_Semantics_2_2_ex7
imports Main
begin

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 => 'a tree2" where
"mirror (Tip x) = Tip x" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

(*Preorder <root> <left> <right>*)
fun pre_order :: "'a tree2 => 'a list" where
"pre_order (Tip x) = [x]" |
"pre_order (Node l a r) = [a] @ (pre_order l) @ (pre_order(r))"

(*Postorder <left> <right> <root>*)
fun post_order :: "'a tree2 => 'a list" where
"post_order (Tip x) = [x]" |
"post_order (Node l a r) = (post_order l) @ (post_order(r)) @ [a]"

(*
 1. \<And>t1 x2 t2.
       pre_order (mirror t1) = rev (post_order t1) \<Longrightarrow>
       pre_order (mirror t2) = rev (post_order t2) \<Longrightarrow>
       rev (post_order t2) @ x2 # rev (post_order t1) =
       rev (post_order t1) @ x2 # rev (post_order t2)
*)
lemma "pre_order (mirror t) = rev (post_order t)"
apply(induction t)
apply(auto)
done

end