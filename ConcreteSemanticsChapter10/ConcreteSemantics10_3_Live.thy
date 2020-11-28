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
(*
       (c\<^sub>1, s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow>
       (\<And>X t. s\<^sub>1 = t on L c\<^sub>1 X \<Longrightarrow> \<exists>t'. (c\<^sub>1, t) \<Rightarrow> t' \<and> s\<^sub>2 = t' on X) \<Longrightarrow>
       (c\<^sub>2, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<Longrightarrow>
       (\<And>X t. s\<^sub>2 = t on L c\<^sub>2 X \<Longrightarrow> \<exists>t'. (c\<^sub>2, t) \<Rightarrow> t' \<and> s\<^sub>3 = t' on X) \<Longrightarrow>
       s\<^sub>1 = t on L (c\<^sub>1;; c\<^sub>2) X \<Longrightarrow> \<exists>t'. (c\<^sub>1;; c\<^sub>2, t) \<Rightarrow> t' \<and> s\<^sub>3 = t' on X
*)
  from Seq.IH(1) Seq.prems obtain t2 where "(c\<^sub>1, t) \<Rightarrow> t2" and "s\<^sub>2 = t2 on L c\<^sub>2 X" 
    by simp blast
  obtain t3 where "(c\<^sub>2, t2) \<Rightarrow> t3" and "s\<^sub>3 = t3 on X" 
    using Seq.IH(2) \<open>s\<^sub>2 = t2 on L c\<^sub>2 X\<close> by blast
  then show ?case 
    using \<open>(c\<^sub>1, t) \<Rightarrow> t2\<close> by blast
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
(*
       bval b s \<Longrightarrow>
       (c\<^sub>1, s) \<Rightarrow> t \<Longrightarrow>
       (\<And>X ta. s = ta on L c\<^sub>1 X \<Longrightarrow> \<exists>t'. (c\<^sub>1, ta) \<Rightarrow> t' \<and> t = t' on X) \<Longrightarrow>
       s = ta on L (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X \<Longrightarrow>
       \<exists>t'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, ta) \<Rightarrow> t' \<and> t = t' on X
*)
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
(*
       \<not> bval b s \<Longrightarrow>
       s = t on L (WHILE b DO c) X \<Longrightarrow> \<exists>t'. (WHILE b DO c, t) \<Rightarrow> t' \<and> s = t' on X
*)
  then have "~ bval b t" 
    by (metis L_While_vars bval_eq_if_eq_on_vars subsetD)
  thus ?case 
    using L_While_X WhileFalse.prems by blast
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
(*
       bval b s\<^sub>1 \<Longrightarrow>
       (c, s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow>
       (\<And>X t. s\<^sub>1 = t on L c X \<Longrightarrow> \<exists>t'. (c, t) \<Rightarrow> t' \<and> s\<^sub>2 = t' on X) \<Longrightarrow>
       (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<Longrightarrow>
       (\<And>X t. s\<^sub>2 = t on L (WHILE b DO c) X \<Longrightarrow>
               \<exists>t'. (WHILE b DO c, t) \<Rightarrow> t' \<and> s\<^sub>3 = t' on X) \<Longrightarrow>
       s\<^sub>1 = t on L (WHILE b DO c) X \<Longrightarrow> \<exists>t'. (WHILE b DO c, t) \<Rightarrow> t' \<and> s\<^sub>3 = t' on X
*)
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

subsection "Program Optimization"

text\<open>Burying assignments to dead variables:\<close>
fun bury :: "com \<Rightarrow> vname set \<Rightarrow> com" where
"bury SKIP X = SKIP" |
"bury (x ::= a) X = (if x \<in> X then x ::= a else SKIP)" |
"bury (c\<^sub>1;; c\<^sub>2) X = (bury c\<^sub>1 (L c\<^sub>2 X);; bury c\<^sub>2 X)" |
"bury (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = IF b THEN bury c\<^sub>1 X ELSE bury c\<^sub>2 X" |
"bury (WHILE b DO c) X = WHILE b DO bury c (L (WHILE b DO c) X)"


(* Lemma 10.19 (Correctness of bury, part 1). *)

theorem bury_correct:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> s = t on L c X \<Longrightarrow>
  \<exists> t'. (bury c X,t) \<Rightarrow> t' & s' = t' on X"
proof (induction arbitrary: X t rule: big_step_induct)
case (Skip s)
then show ?case by auto
next
  case (Assign x a s)
  then show ?case by (auto simp add: ball_Un)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from Seq.IH(1) Seq.prems obtain t2 where "(bury c\<^sub>1 (L c\<^sub>2 X), t) \<Rightarrow> t2" and "s\<^sub>2 = t2 on L c\<^sub>2 X" 
    by simp blast
  obtain t3 where "(bury c\<^sub>2 X, t2) \<Rightarrow> t3" and "s\<^sub>3 = t3 on X" 
    by (metis Seq.IH(2) \<open>(bury c\<^sub>1 (L c\<^sub>2 X), t) \<Rightarrow> t2\<close> \<open>\<And>thesis. (\<And>t2. \<lbrakk>(bury c\<^sub>1 (L c\<^sub>2 X), t) \<Rightarrow> t2; s\<^sub>2 = t2 on L c\<^sub>2 X\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> big_step_determ)
  then show ?case 
    using \<open>(bury c\<^sub>1 (L c\<^sub>2 X), t) \<Rightarrow> t2\<close> by auto
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  then have "s = t on vars b" and "s = t on L c\<^sub>1 X " by auto
  have "bval b t" 
    using IfTrue.hyps(1) \<open>s = t on vars b\<close> bval_eq_if_eq_on_vars by blast
  from IfTrue.IH[OF \<open>s = t on L c\<^sub>1 X\<close>] obtain t' where
    "(bury c\<^sub>1 X, t) \<Rightarrow> t'" "s' =t' on X" by auto
  then show ?case 
    using \<open>bval b t\<close> by auto
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  then have "s = t on vars b" and "s = t on L c\<^sub>2 X " by auto
  have "\<not> bval b t" 
    using IfFalse.hyps(1) \<open>s = t on vars b\<close> bval_eq_if_eq_on_vars by blast
 from IfFalse.IH[OF \<open>s = t on L c\<^sub>2 X\<close>] obtain t' where "s' = t' on X"  "(bury c\<^sub>2 X, t) \<Rightarrow> t'" by auto
  then show ?case using \<open>\<not> bval b t\<close> 
    by auto
next
  case (WhileFalse b s c)
  then have "\<not> bval b t" 
    by (metis L_While_vars bval_eq_if_eq_on_vars subsetD)
  thus ?case 
    using L_While_X WhileFalse.prems by fastforce
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?w = "WHILE b DO c"
  have "bval b t" 
    by (metis L_While_vars WhileTrue.hyps(1) WhileTrue.prems bval_eq_if_eq_on_vars subsetD)
  then have "s\<^sub>1 = t on L c (L ?w X)" 
    using L_While_pfp WhileTrue.prems by blast
  obtain t2 where "(bury c (L ?w X), t) \<Rightarrow> t2" "s\<^sub>2 = t2 on L ?w X" 
    using WhileTrue.IH(1) \<open>s\<^sub>1 = t on L c (L (WHILE b DO c) X)\<close> by blast
  obtain t3 where "(bury ?w X, t2) \<Rightarrow> t3" "s\<^sub>3 = t3 on X" 
    using WhileTrue.IH(2) \<open>s\<^sub>2 = t2 on L (WHILE b DO c) X\<close> by blast
  then show ?case 
    using \<open>(bury c (L (WHILE b DO c) X), t) \<Rightarrow> t2\<close> \<open>bval b t\<close> by auto
qed



end