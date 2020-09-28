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
  





end