theory Concrete_Semantics_2_2_ex8
imports Main
begin

fun intersperse :: "'a => 'a list => 'a list" where
"intersperse a [] = []" |
"intersperse a (x # Nil) = [x]" |
"intersperse a (x # xs) = (x # [a]) @ intersperse a xs"

value "intersperse (1::nat) ([2,3,4]::nat list)"

(* intersperse is recursive function. *)
lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs rule: intersperse.induct)
apply(auto)
done

end