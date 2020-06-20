theory Concrete_Semantics_2_2_ex5
imports Main
begin

fun sum_upto :: "nat => nat" where
"sum_upto 0 = 0" |
"sum_upto n = n + sum_upto (n - 1)"

lemma "sum_upto n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
done

end