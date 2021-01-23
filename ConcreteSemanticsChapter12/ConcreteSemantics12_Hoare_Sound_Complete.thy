theory ConcreteSemantics12_Hoare_Sound_Complete
  imports "~~/src/HOL/IMP/Hoare"
begin

subsection \<open>Soundness and Completeness\<close>

subsubsection "Soundness"

lemma hoare_sound: "\<turnstile> {P}c{Q}  \<Longrightarrow>  \<Turnstile> {P}c{Q}"
proof(induction rule: hoare.induct)
case (Skip P)
  then show ?case 
    using hoare_valid_def by auto
next
  case (Assign P a x)
  then show ?case 
    using hoare_valid_def by auto
next
  case (Seq P c\<^sub>1 Q c\<^sub>2 R)
  then show ?case 
    using hoare_valid_def by auto
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  then show ?case 
    using hoare_valid_def by auto
next
  case (While P b c)
  have "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> P s \<Longrightarrow> P t \<and> \<not> bval b t" for s t 
  proof(induction "WHILE b DO c" s t rule: big_step_induct)
    case (WhileFalse s)
    then show ?case 
      by simp
  next
    case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
    then show ?case 
      using While.IH hoare_valid_def by auto
  qed
  then show ?case 
    using hoare_valid_def by auto
next
  case (conseq P' P c Q Q')
  then show ?case 
    using hoare_valid_def by auto
qed 

subsubsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
  apply(auto simp: wp_def)
  done

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
(*  apply(auto simp: wp_def)
  done*)
  by (rule ext) (auto simp: wp_def)

lemma wp_Seq[simp]: "wp (c\<^sub>1;;c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
(*  apply(auto simp: wp_def)
  done*)
  by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q =
 (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
(*  apply(auto simp: wp_def)
  done*)
  by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
(*  apply(auto simp: wp_def)
  by (simp add: while_unfold)*)
  unfolding wp_def by (metis unfold_while)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
(*    apply(auto simp: wp_def)
  done*)
  by (auto simp: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
(*    apply(auto simp: wp_def)
  done*)
  by (auto simp: wp_While_If)

end