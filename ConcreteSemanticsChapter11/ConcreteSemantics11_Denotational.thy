theory ConcreteSemantics11_Denotational
  imports Main "~~/src/HOL/IMP/Big_Step"
begin 

section "Denotational Semantics of Commands"

type_synonym com_den = "(state \<times> state) set"

definition W :: "(state \<Rightarrow> bool) \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
"W db dc = (\<lambda>dw. {(s,t). if db s then (s, t) \<in> dc O dw else s = t})"

fun D :: "com \<Rightarrow> com_den" where
"D SKIP   = Id" |
"D (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"D (c1;;c2)  = D(c1) O D(c2)" |
"D (IF b THEN c1 ELSE c2)
 = {(s,t). if bval b s then (s,t) \<in> D c1 else (s,t) \<in> D c2}" |
"D (WHILE b DO c) = lfp (W (bval b) (D c))"

lemma W_mono: "mono (W b r)"
  apply(unfold mono_def W_def)
  apply(auto)
  done

lemma D_While_If:
  "D(WHILE b DO c) = D(IF b THEN c;;WHILE b DO c ELSE SKIP)"
proof -
  let ?w = "WHILE b DO c"
  let ?f = "W (bval b) (D c)"
  have "D ?w = lfp ?f" 
    by simp
  also have "... = ?f (lfp ?f)" 
    by (simp add: W_mono def_lfp_unfold)
(*  also have "... = ?f (D ?w)" 
    by simp*)
  also have "... = D(IF b THEN c;;WHILE b DO c ELSE SKIP)" 
    using W_def by auto
  then show ?thesis 
    using calculation by auto
    (*using \<open>lfp (W (bval b) (D c)) = W (bval b) (D c) (lfp (W (bval b) (D c)))\<close> by auto*)
qed

text\<open>Equivalence of denotational and big-step semantics:\<close>

(*Lemma 11.4.*)
lemma D_if_big_step:  "(c,s) \<Rightarrow> t \<Longrightarrow> (s,t) \<in> D(c)"
proof(induction rule: big_step_induct)
case (Skip s)
  then show ?case 
    by simp
next
  case (Assign x a s)
  then show ?case 
    by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case 
    by auto
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case 
    by simp
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case 
    by simp
next
  case (WhileFalse b s c)
  then show ?case 
    using D_While_If by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case 
  proof -
    have "(s\<^sub>1, s\<^sub>3) \<in> D (c;; WHILE b DO c)"
      using D.simps(3) WhileTrue.IH(1) WhileTrue.IH(2) by blast
    then show ?thesis
      using D_While_If WhileTrue.hyps(1) by force
  qed
qed

abbreviation Big_step :: "com \<Rightarrow> com_den" where
"Big_step c \<equiv> {(s,t). (c,s) \<Rightarrow> t}"

(*Lemma 11.5.*)
lemma Big_step_if_D:  "(s,t) \<in> D(c) \<Longrightarrow> (s,t) \<in> Big_step c"
proof(induction c arbitrary: s t)
case SKIP
  then show ?case 
    by auto
next
  case (Assign x1 x2)
  then show ?case by fastforce
next
  case (Seq c1 c2)
  then show ?case by fastforce
next
  case (If x1 c1 c2)
  then show ?case by (auto split: if_splits)
next
  case (While b c)
  let ?B = "Big_step (WHILE b DO c)"
  let ?f = "W (bval b) (D c)"
  have "?f ?B \<subseteq> ?B" using While.IH by (auto simp: W_def)
  then show ?case 
    using D.simps(5) While.prems lfp_lowerbound by blast
qed

end