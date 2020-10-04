theory Concrete_Semantics_2_2_ex6
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree => 'a list" where
"contents Tip = []" |
"contents (Node l a r) = (contents r) @ (a # (contents l))"

fun sum_tree :: "nat tree => nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"

lemma "sum_tree t = sum_list (contents t)"
apply(induction t)
apply(auto)
done

end