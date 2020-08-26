theory ConcreteSemantics8_1_Stack
  imports Main "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Star"
begin

text \<open>

> Working with proofs on the machine language, we will find it convenient for the program counter to admit negative values, 
> The effect of this choice is that various decomposition lemmas about machine executions have nicer algebraic properties and fewer preconditions than their nat counterparts

  In the following, we use the length of lists as integers 
  instead of natural numbers. Instead of converting \<^typ>\<open>nat\<close>
  to \<^typ>\<open>int\<close> explicitly, we tell Isabelle to coerce \<^typ>\<open>nat\<close>
  automatically when necessary.
\<close>
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

text\<open>
Missing patterns in function definition:
\<And>b. [] !! b = undefined 
Found termination order: "(\<lambda>p. length (fst p)) <*mlex*> {}"
\<close>

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a"(infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

text\<open>
Type unification failed: Clash of types "nat" and "int"

Type error in application: incompatible operand type

Operator:  (<) i :: int \<Rightarrow> bool
Operand:   length xs :: nat

This problem is solved by set declare in top of this theory.
\<close>
lemma "0 \<le> i \<Longrightarrow> (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
  apply(induction xs arbitrary: i)
   apply (auto simp add: algebra_simps)
  done

end