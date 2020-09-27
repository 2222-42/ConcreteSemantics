theory ConcreteSemantics9_2_Sec_Typing
  imports Main "~~/src/HOL/IMP/Sec_Type_Expr" 
begin 

subsubsection "Syntax Directed Typing"

inductive sec_type :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile> _)" [0,0] 50) where
Skip:
  "l \<turnstile> SKIP" |
Assign:
  "\<lbrakk> sec x \<ge> sec a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile> x ::= a" |
Seq:
  "\<lbrakk> l \<turnstile> c\<^sub>1;  l \<turnstile> c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> c\<^sub>1;;c\<^sub>2" |
If:
  "\<lbrakk> max (sec b) l \<turnstile> c\<^sub>1;  max (sec b) l \<turnstile> c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" |
While:
  "max (sec b) l \<turnstile> c \<Longrightarrow> l \<turnstile> WHILE b DO c"

code_pred (expected_modes: i => i => bool) sec_type .

value "0 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"
value "0 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x''  ::= N 0 ELSE SKIP"
value "1 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x''  ::= N 0 ELSE SKIP"
value "1 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"
value "2 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"
value "3 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"

inductive_cases [elim!]:
  "l \<turnstile> x ::= a"  "l \<turnstile> c\<^sub>1;;c\<^sub>2"  "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"  "l \<turnstile> WHILE b DO c"

text\<open>An important property: anti-monotonicity.\<close>

(* Lemma 9.12 (Anti-monotonicity). *)
lemma anti_mono: "\<lbrakk> l \<turnstile> c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile> c"
  apply(induction arbitrary: l' rule:sec_type.induct)
      apply (simp add: sec_type.Skip)
  using sec_type.Assign apply auto[1]
    apply (simp add: sec_type.Seq)
  using If apply auto[1]
  by (simp add: While)

(* Lemma 9.13 (Confinement). *)
lemma confinement: "\<lbrakk> (c,s) \<Rightarrow> t;  l \<turnstile> c \<rbrakk> \<Longrightarrow> s = t (< l)"
proof(induction rule: big_step_induct)
case (Skip s)
  then show ?case 
    by simp
next
  case (Assign x a s)
  then show ?case by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by auto
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  hence "max (sec b) l \<turnstile> c\<^sub>1" 
    by blast
  hence "l \<turnstile> c\<^sub>1" 
    using anti_mono max.cobounded2 by blast
  thus ?case 
    by (simp add: IfTrue.IH)
(*
  then show ?case 
    by (smt anti_mono com.distinct(11) com.distinct(15) com.distinct(19) com.distinct(5) com.inject(3) max.cobounded2 sec_type.cases) *)
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  hence "max (sec b) l \<turnstile> c\<^sub>2" 
    by blast
  hence "l \<turnstile> c\<^sub>2" 
    using anti_mono max.cobounded2 by blast
  thus ?case 
    by (simp add: IfFalse.IH)
next
  case (WhileFalse b s c)
  then show ?case 
    by blast
next
  case (WhileTrue b s\<^sub>1 c)
  hence "max (sec b) l \<turnstile> c" 
    by blast
  hence "l \<turnstile> c" 
    by (simp add: anti_mono)
  then show ?case 
    by (simp add: WhileTrue.IH(1) WhileTrue.IH(2) WhileTrue.prems)
qed

(* Theorem 9.14 (Noninterference). *)
theorem noninterference:
  "\<lbrakk> (c,s) \<Rightarrow> s'; (c,t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (\<le> l) \<rbrakk>
   \<Longrightarrow> s' = t' (\<le> l)"
proof(induction arbitrary: t t' rule: big_step_induct)
case (Skip s)
  then show ?case by auto
next
  case (Assign x a s)
  have [simp]:"t' = t(x := aval a t)" using Assign by auto
  have "sec a \<le> sec x"  using \<open>0 \<turnstile> x ::= a\<close> by auto
  show ?case 
  proof auto
(* 1. sec x \<le> l \<Longrightarrow> aval a s = aval a t
 2. \<And>xa. xa \<noteq> x \<Longrightarrow> sec xa \<le> l \<Longrightarrow> s xa = t xa*)
    assume " sec x \<le> l"
    have "sec a \<le> l" 
      using \<open>sec a \<le> sec x\<close> \<open>sec x \<le> l\<close> le_trans by blast
    thus " aval a s = aval a t" 
      using Assign.prems(3) aval_eq_if_eq_le by blast
  next
    fix xa assume "xa \<noteq> x" "sec xa \<le> l"
    thus "s xa = t xa" 
      by (simp add: Assign.prems(3))
  qed
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