theory Concrete_Semantics_2_2_ex3
imports Main
begin

fun count :: "'a => 'a list => nat" where
"count a Nil = 0" |
"count a (x # xs) = (if a = x then 1 else 0) + count a xs"

lemma "count x xs \<le> length xs"
apply(induction xs)
apply(auto)
done

end