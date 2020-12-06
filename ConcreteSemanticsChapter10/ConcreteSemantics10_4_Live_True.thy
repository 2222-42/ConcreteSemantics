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

lemma mono_union_L:
  "mono (\<lambda>Y. X \<union> L c Y)"
  by (smt L_mono le_iff_sup le_sup_iff monoI mono_Un sup.idem sup.mono)

lemma L_While_unfold: "L (WHILE b DO c) X = vars b \<union> X \<union> L c (L (WHILE b DO c) X)"
  apply(metis lfp_unfold[OF mono_union_L] L.simps(5))
  done
(*
 1. lfp (\<lambda>Y. vars b \<union> X \<union> L c Y) = vars b \<union> X \<union> L c (lfp (\<lambda>Y. vars b \<union> X \<union> L c Y)) 
*)

lemma L_While_pfp: "L c (L (WHILE b DO c) X) \<subseteq> L (WHILE b DO c) X"
  using L_While_unfold by blast

lemma L_While_vars: "vars b \<subseteq> L (WHILE b DO c) X"
  using L_While_unfold by auto

lemma L_While_X: "X \<subseteq> L (WHILE b DO c) X"
  using L_While_unfold by auto


subsubsection "Correctness"
(*Lemma 10.31 (Correctness of L).*)
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
  from Seq.IH(1) Seq.prems obtain t2 where "(c\<^sub>1, t) \<Rightarrow> t2" and "s\<^sub>2 = t2 on L c\<^sub>2 X" 
    by simp blast
  obtain t3 where "(c\<^sub>2, t2) \<Rightarrow> t3" and "s\<^sub>3 = t3 on X" 
    using Seq.IH(2) \<open>s\<^sub>2 = t2 on L c\<^sub>2 X\<close> by blast
  then show ?case 
    using \<open>(c\<^sub>1, t) \<Rightarrow> t2\<close> by blast
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  then have "s = t on vars b" and "s = t on L c\<^sub>1 X " by auto
  have "bval b t" 
    using IfTrue.hyps(1) \<open>s = t on vars b\<close> bval_eq_if_eq_on_vars by blast
 from IfTrue.IH[OF \<open>s = t on L c\<^sub>1 X\<close>] obtain t' where "s' = t' on X"  "(c\<^sub>1, t) \<Rightarrow> t'" by auto
  then show ?case 
    using \<open>bval b t\<close> by blast
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  then have "s = t on vars b" and "s = t on L c\<^sub>2 X " by auto
  have "\<not> bval b t" 
    using IfFalse.hyps(1) \<open>s = t on vars b\<close> bval_eq_if_eq_on_vars by blast
 from IfFalse.IH[OF \<open>s = t on L c\<^sub>2 X\<close>] obtain t' where "s' = t' on X"  "(c\<^sub>2, t) \<Rightarrow> t'" by auto
  then show ?case using \<open>\<not> bval b t\<close> by blast
next
  case (WhileFalse b s c)
  then have "~ bval b t" 
    by (metis L_While_vars bval_eq_if_eq_on_vars subsetD)
  thus ?case 
    using L_While_X WhileFalse.prems by blast
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?w = "WHILE b DO c"
  have "bval b t" 
    by (metis L_While_vars WhileTrue.hyps(1) WhileTrue.prems bval_eq_if_eq_on_vars subsetD)
  then have "s\<^sub>1 = t on L c (L ?w X)" 
    using L_While_pfp WhileTrue.prems by blast
  obtain t2 where "(c, t) \<Rightarrow> t2" "s\<^sub>2 = t2 on L ?w X" 
    using WhileTrue.IH(1) \<open>s\<^sub>1 = t on L c (L (WHILE b DO c) X)\<close> by blast
  obtain t3 where "(?w, t2) \<Rightarrow> t3" "s\<^sub>3 = t3 on X" 
    using WhileTrue.IH(2) \<open>s\<^sub>2 = t2 on L (WHILE b DO c) X\<close> by blast
  then show ?case 
    using \<open>(c, t) \<Rightarrow> t2\<close> \<open>bval b t\<close> by blast
qed

end