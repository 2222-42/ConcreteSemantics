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

value "show (L (''y'' ::= V ''z'';; ''x'' ::= Plus (V ''y'') (V ''z'')) {''x''})"

value "show (L (WHILE Less (V ''x'') (V ''x'') DO ''y'' ::= V ''z'') {''x''})"

fun "kill" :: "com \<Rightarrow> vname set" where
"kill SKIP = {}" |
"kill (x ::= a) = {x}" |
"kill (c\<^sub>1;; c\<^sub>2) = kill c\<^sub>1 \<union> kill c\<^sub>2" |
"kill (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = kill c\<^sub>1 \<inter> kill c\<^sub>2" |
"kill (WHILE b DO c) = {}"

fun gen :: "com \<Rightarrow> vname set" where
"gen SKIP = {}" |
"gen (x ::= a) = vars a" |
"gen (c\<^sub>1;; c\<^sub>2) = gen c\<^sub>1 \<union> (gen c\<^sub>2 - kill c\<^sub>1)" |
"gen (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = vars b \<union> gen c\<^sub>1 \<union> gen c\<^sub>2" |
"gen (WHILE b DO c) = vars b \<union> gen c"

(* Lemma 10.15 (Liveness via gen/kill). *)
lemma L_gen_kill: "L c X = gen c \<union> (X - kill c)"
proof(induction c arbitrary:X)
  case SKIP
then show ?case by auto
next
  case (Assign x1 x2)
  then show ?case by auto
next
  case (Seq c1 c2)
  then show ?case by auto
next
  case (If x1 c1 c2)
  then show ?case by auto
next
  case (While x1 c)
  then show ?case by auto
qed

(*Lemma 10.15 (Liveness via gen/kill).*)
lemma L_While_pfp: "L c (L (WHILE b DO c) X) \<subseteq> L (WHILE b DO c) X"
  apply(auto simp add: L_gen_kill)
  done


end