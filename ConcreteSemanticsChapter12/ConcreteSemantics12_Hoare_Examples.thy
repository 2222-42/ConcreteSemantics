theory ConcreteSemantics12_Hoare_Examples
  imports "~~/src/HOL/IMP/Hoare"
begin

fun sum:: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1) + i)"

text\<open>To prove while_sum, it is needed to prove the following lemma and declare sum.simps\<close>
lemma sum_simps[simp]: 
"0 < i \<Longrightarrow> sum i = sum (i - 1) + i"
"i \<le> 0 \<Longrightarrow> sum i = 0"
   apply(simp_all)
  done

declare sum.simps[simp del]

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'') DO 
  (''y''::= Plus (V ''y'') (V ''x'');;''x''::= Plus (V ''x'') (N (-1)))
"

lemma while_sum: "(wsum, s) \<Rightarrow> t \<Longrightarrow> t ''y'' = s ''y'' + sum (s ''x'')"
  apply(induction wsum s t rule: big_step_induct)
   apply(auto)
  done

lemma sum_via_bigstep: 
  assumes "(''y''::= N 0;; wsum, s) \<Rightarrow> t"
  shows " t ''y'' = sum (s ''x'')"
proof -
  from assms have "(wsum, s(''y'' := 0)) \<Rightarrow> t" by auto
  then show ?thesis 
    using while_sum by fastforce
qed

lemma "\<turnstile> {\<lambda>s. s ''x'' = n} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = sum n}"
  apply(rule Seq)
   prefer 2
   apply(rule While' [where P = "\<lambda>s. s ''y'' = sum n - sum(s ''x'')"])
    apply(rule Seq)
     prefer 2
     apply(rule Assign)
    apply(rule Assign')
    apply(simp_all)
  apply(rule Assign')
  apply(simp)
  done


end