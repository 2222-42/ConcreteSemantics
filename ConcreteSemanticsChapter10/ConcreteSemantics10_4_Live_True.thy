theory ConcreteSemantics10_4_Live_True
  imports Main "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Vars" "~~/src/HOL/Library/While_Combinator"  
begin 

subsection "True Liveness Analysis"

subsubsection "Analysis"

fun L :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"L SKIP X = X" |
"L (x ::= a) X = (if x \<in> X then vars a \<union> (X - {x}) else X)" |
"L (c\<^sub>1;; c\<^sub>2) X = L c\<^sub>1 (L c\<^sub>2 X)" |
"L (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = vars b \<union> L c\<^sub>1 X \<union> L c\<^sub>2 X" |
"L (WHILE b DO c) X = lfp(\<lambda>Y. vars b \<union> X \<union> L c Y)"

(*Lemma 10.30.*)
lemma L_mono: "mono(L c)"
proof-
  have "X \<subseteq> Y \<Longrightarrow> L c X \<subseteq> L c Y" for X Y
  proof (induction c arbitrary: X Y)
  case SKIP
    then show ?case 
      by (simp add: monoI)
  next
    case (Assign x1 x2)
    then show ?case by auto
  next
    case (Seq c1 c2)
    then show ?case 
      by simp
  next
    case (If x1 c1 c2)
    then show ?case by (simp add: subset_iff)
  next
    case (While x1 c)
    show ?case 
    proof(simp, rule lfp_mono)
      fix Z show "vars x1 \<union> X \<union> L c Z \<subseteq> vars x1 \<union> Y \<union> L c Z" 
        using While.prems by auto
    qed
  qed
  thus ?thesis 
    by (simp add: monoI)
qed

end