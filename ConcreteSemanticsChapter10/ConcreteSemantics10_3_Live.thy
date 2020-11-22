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

lemma L_While_lpfp:
  "vars b \<union> X \<union> L c P \<subseteq> P \<Longrightarrow> L (WHILE b DO c) X \<subseteq> P"
by(simp add: L_gen_kill)

lemma L_While_vars: "vars b \<subseteq> L (WHILE b DO c) X"
by auto

lemma L_While_X: "X \<subseteq> L (WHILE b DO c) X"
by auto

text\<open>Disable L WHILE equation and reason only with L WHILE constraints\<close>
declare L.simps(5)[simp del]

subsection "Correctness"

theorem L_correct:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> s = t on L c X \<Longrightarrow>
  \<exists> t'. (c,t) \<Rightarrow> t' & s' = t' on X"
proof (induction arbitrary: X t rule: big_step_induct)
case (Skip s)
  then show ?case by auto
next
  case (Assign x a s)
  then show ?case by (auto simp add: ball_Un)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case sorry
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case sorry
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case sorry
next
  case (WhileFalse b s c)
  then show ?case sorry
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case sorry
qed

end