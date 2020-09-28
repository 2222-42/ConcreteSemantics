subsection "Termination-Sensitive Systems"

theory ConcreteSemantics9_2_Sec_TypingT
  imports Main "~~/src/HOL/IMP/Sec_Type_Expr" 
begin 

subsubsection "A Syntax Directed System"

inductive sec_type :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile> _)" [0,0] 50) where
Skip:
  "l \<turnstile> SKIP"  |
Assign:
  "\<lbrakk> sec x \<ge> sec a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile> x ::= a"  |
Seq:
  "l \<turnstile> c\<^sub>1 \<Longrightarrow> l \<turnstile> c\<^sub>2 \<Longrightarrow> l \<turnstile> c\<^sub>1;;c\<^sub>2"  |
If:
  "\<lbrakk> max (sec b) l \<turnstile> c\<^sub>1;  max (sec b) l \<turnstile> c\<^sub>2 \<rbrakk>
   \<Longrightarrow> l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"  |
While:
  "sec b = 0 \<Longrightarrow> 0 \<turnstile> c \<Longrightarrow> 0 \<turnstile> WHILE b DO c"

code_pred (expected_modes: i => i => bool) sec_type .

inductive_cases [elim!]:
  "l \<turnstile> x ::= a"  "l \<turnstile> c\<^sub>1;;c\<^sub>2"  "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"  "l \<turnstile> WHILE b DO c"

(* Lemma 9.19 (Anti-monotonicity). *)
lemma anti_mono: "l \<turnstile> c \<Longrightarrow> l' \<le> l \<Longrightarrow> l' \<turnstile> c"
  apply(induction arbitrary: l' rule:sec_type.induct)
      apply(simp add: Skip)
     apply(simp add: Assign)
    apply(simp add: Seq)
   apply (simp add: If)
  by(simp add: While)
  

(* Lemma 9.20 (Confinement). *)
lemma confinement: "(c,s) \<Rightarrow> t \<Longrightarrow> l \<turnstile> c \<Longrightarrow> s = t (< l)"
proof(induction rule: big_step_induct)
  case (Skip s)
  then show ?case by simp
next
  case (Assign x a s)
  then show ?case by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by auto
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then have "max (sec b) l \<turnstile> c\<^sub>1" by blast
  then have "l \<turnstile> c\<^sub>1" 
    using anti_mono max.cobounded2 by blast
  then show ?case 
    by (simp add: IfTrue.IH)
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then have "max (sec b) l \<turnstile> c\<^sub>2" by blast
  then have "l \<turnstile> c\<^sub>2" 
    using anti_mono max.cobounded2 by blast
  then show ?case 
    by (simp add: IfFalse.IH)
(*    by (smt anti_mono com.distinct(11) com.distinct(15) com.distinct(19) com.distinct(5) com.inject(3) max.orderI max_def sec_type.simps)*)
next
  case (WhileFalse b s c)
  then show ?case by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case by auto
qed

(* Lemma 9.21 (Termination). *)
lemma termi_if_non0: "l \<turnstile> c \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> \<exists> t. (c,s) \<Rightarrow> t"
  apply(induction arbitrary: s rule: sec_type.induct)
      apply(simp add: big_step.Skip)
  apply auto
   apply blast
  by (metis IfFalse IfTrue max.commute max.strict_coboundedI1)

(* Theorem 9.22 (Noninterference). *)
theorem noninterference: "(c,s) \<Rightarrow> s' \<Longrightarrow> 0 \<turnstile> c \<Longrightarrow>  s = t (\<le> l)
  \<Longrightarrow> \<exists> t'. (c,t) \<Rightarrow> t' \<and> s' = t' (\<le> l)"
proof(induction arbitrary: t rule: big_step_induct)
case (Skip s)
  then show ?case by auto
next
  case (Assign x a s)
  have "sec a \<le> sec x" using \<open>0 \<turnstile> x ::= a\<close> by auto
  have "(x ::= a, t) \<Rightarrow> t(x := aval a t)" using Assign by auto
  moreover have "s(x := aval a s) = t(x := aval a t)" sorry
  then show ?case 
    by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by blast
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