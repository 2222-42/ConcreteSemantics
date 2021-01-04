theory ConcreteSemantics12_Hoare_Examples
  imports "~~/src/HOL/IMP/Hoare"
begin

fun sum:: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1) + 1)"

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'') DO 
  (''y''::= Plus (V ''y'') (V ''x'');;''x''::= Plus (V ''x'') (N (-1)))
"

lemma while_sum: "(wsum, s) \<Rightarrow> t \<Longrightarrow> t ''y'' = s ''y'' + sum (s ''x'')"
  sorry

lemma sum_via_bigste: 
  assumes "(''y''::= N 0;; wsum, s) \<Rightarrow> t"
  shows " t ''y'' = sum (s ''x'')"
  sorry
end