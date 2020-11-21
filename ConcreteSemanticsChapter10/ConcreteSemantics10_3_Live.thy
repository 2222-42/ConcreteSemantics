theory ConcreteSemantics10_3_Live
  imports Main "~~/src/HOL/IMP/Big_Step"  "~~/src/HOL/IMP/Vars" 
begin 

subsection "Liveness Analysis"

fun L :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"L SKIP X = X" |
"L (x ::= a) X = vars a \<union> (X - {x})" |
"L (c\<^sub>1;; c\<^sub>2) X = L c\<^sub>1 (L c\<^sub>2 X)" |
"L (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = vars b \<union> L c\<^sub>1 X \<union> L c\<^sub>2 X" |
"L (WHILE b DO c) X = vars b \<union> X \<union> L c X"

end