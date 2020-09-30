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
  moreover 
  have "s(x := aval a s) = t(x := aval a t) (\<le> l)" 
    using Assign.prems(2) \<open>sec a \<le> sec x\<close> aval_eq_if_eq_le by auto
  then show ?case 
    by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by blast
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
(*    bval b s
    (c\<^sub>1, s) \<Rightarrow> s'
    0 \<turnstile> c\<^sub>1 \<Longrightarrow> s = ?t (\<le> l) \<Longrightarrow> \<exists>t'. (c\<^sub>1, ?t) \<Rightarrow> t' \<and> s' = t' (\<le> l)
    0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2
    s = t (\<le> l)*)
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  obtain t' where t': "(c\<^sub>1, t) \<Rightarrow> t'" "s' = t' (\<le> l)"
    using IfTrue.IH[OF anti_mono[OF \<open>sec b \<turnstile> c\<^sub>1\<close>] \<open>s = t (\<le> l)\<close>] by blast
  show ?case 
  proof cases
    assume "sec b \<le> l"
(*\<exists>t'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<Rightarrow> t' \<and> ta__ = t' (\<le> l)*)
    then have "s = t (\<le> sec b)" 
      using IfTrue.prems(2) dual_order.trans by blast
    hence "bval b t" 
      using IfTrue.hyps(1) bval_eq_if_eq_le by auto
    then show ?thesis 
      using t'(1) t'(2) by blast
  next
    assume "\<not> sec b \<le> l"
(*\<exists>t'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<Rightarrow> t' \<and> ta__ = t' (\<le> l)*)
    then have 0: "sec b \<noteq> 0" 
      using \<open>\<not> sec b \<le> l\<close> by auto
    have 1: "sec b \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" 
      by (simp add: If \<open>sec b \<turnstile> c\<^sub>1\<close> \<open>sec b \<turnstile> c\<^sub>2\<close>)
    from confinement[OF big_step.IfTrue[OF IfTrue(1,2)] 1] \<open>\<not> sec b \<le> l\<close>
    have "s = s'(\<le> l)" by auto
    (* we first have to show that the second execution terminates,*)
    moreover obtain t' where t' : "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<Rightarrow> t'" 
      by (meson "0" "1" termi_if_non0)
    moreover have "t = t' (\<le> l)" 
      using "1" \<open>\<not> sec b \<le> l\<close> confinement t' by auto
(*      using "1" \<open>\<not> sec b \<le> l\<close> confinement by auto*)
    ultimately show ?thesis 
      using IfTrue.prems(2) by auto
  qed
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
(*    \<not> bval b s
    (c\<^sub>2, s) \<Rightarrow> ta__
    0 \<turnstile> c\<^sub>2 \<Longrightarrow> s = ?t (\<le> l) \<Longrightarrow> \<exists>t'. (c\<^sub>2, ?t) \<Rightarrow> t' \<and> ta__ = t' (\<le> l)
    0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2
    s = t (\<le> l)*)
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  obtain t' where t': "(c\<^sub>2, t) \<Rightarrow> t'" "s' = t' (\<le> l)" 
    using IfFalse.IH[OF anti_mono[OF \<open>sec b \<turnstile> c\<^sub>2\<close>] \<open>s = t (\<le> l)\<close>] by blast
  show ?case 
  proof cases
    assume "sec b \<le> l"
(*\<exists>t'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<Rightarrow> t' \<and> ta__ = t' (\<le> l)*)
    then have "s = t (\<le> sec b)" 
      using IfFalse.prems(2) dual_order.trans by blast
    hence "\<not> bval b t" 
      using IfFalse.hyps(1) bval_eq_if_eq_le by auto
    then show ?thesis 
      using t'(1) t'(2) by blast
  next
    assume "\<not> sec b \<le> l"
(*\<exists>t'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<Rightarrow> t' \<and> ta__ = t' (\<le> l)*)
    then have 0: "sec b \<noteq> 0" 
      using \<open>\<not> sec b \<le> l\<close> by auto
    have 1: "sec b \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" 
      by (simp add: If \<open>sec b \<turnstile> c\<^sub>1\<close> \<open>sec b \<turnstile> c\<^sub>2\<close>)
    from confinement[OF big_step.IfFalse[OF IfFalse(1,2)] 1] \<open>\<not> sec b \<le> l\<close>
    have "s = s'(\<le> l)" by auto
    (* we first have to show that the second execution terminates,*)
    moreover obtain t' where t' : "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<Rightarrow> t'" 
      by (meson "0" "1" termi_if_non0)
    moreover have "t = t' (\<le> l)" 
      using "1" \<open>\<not> sec b \<le> l\<close> confinement t' by auto
(*      using "1" \<open>\<not> sec b \<le> l\<close> confinement by auto*)
    ultimately show ?thesis 
      using IfFalse.prems(2) by auto
  qed
next
  case (WhileFalse b s c)
(*  \<not> bval b s
    0 \<turnstile> WHILE b DO c
    s = t (\<le> l)*)
  then have [simp]: "sec b = 0" by auto
  then have "s = t (\<le> l)" 
    by (simp add: WhileFalse.prems(2))
  then have "\<not> bval b t" 
    using WhileFalse.hyps bval_eq_if_eq_le by auto
  then show ?case 
    using WhileFalse.prems(2) by blast
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
(*
this:
    bval b s\<^sub>1
    (c, s\<^sub>1) \<Rightarrow> s\<^sub>2
    (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3
    0 \<turnstile> c \<Longrightarrow> s\<^sub>1 = ?t (\<le> l) \<Longrightarrow> \<exists>t'. (c, ?t) \<Rightarrow> t' \<and> s\<^sub>2 = t' (\<le> l)
    0 \<turnstile> WHILE b DO c \<Longrightarrow> s\<^sub>2 = ?t (\<le> l) \<Longrightarrow> \<exists>t'. (WHILE b DO c, ?t) \<Rightarrow> t' \<and> s\<^sub>3 = t' (\<le> l)
    0 \<turnstile> WHILE b DO c
    s\<^sub>1 = t (\<le> l)

goal (1 subgoal):
 1. \<And>b s\<^sub>1 c s\<^sub>2 s\<^sub>3 t.
       bval b s\<^sub>1 \<Longrightarrow>
       (c, s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow>
       (\<And>t. 0 \<turnstile> c \<Longrightarrow> s\<^sub>1 = t (\<le> l) \<Longrightarrow> \<exists>t'. (c, t) \<Rightarrow> t' \<and> s\<^sub>2 = t' (\<le> l)) \<Longrightarrow>
       (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<Longrightarrow>
       (\<And>t. 0 \<turnstile> WHILE b DO c \<Longrightarrow> s\<^sub>2 = t (\<le> l) \<Longrightarrow> \<exists>t'. (WHILE b DO c, t) \<Rightarrow> t' \<and> s\<^sub>3 = t' (\<le> l)) \<Longrightarrow>
       0 \<turnstile> WHILE b DO c \<Longrightarrow> s\<^sub>1 = t (\<le> l) \<Longrightarrow> \<exists>t'. (WHILE b DO c, t) \<Rightarrow> t' \<and> s\<^sub>3 = t' (\<le> l)
*)
  let ?w = "WHILE b DO c"
  from \<open>0 \<turnstile> ?w\<close> have [simp]: "sec b = 0" by auto
  have "0 \<turnstile> c" 
    using WhileTrue.prems(1) by blast
  obtain t'' where t'': "(c, t) \<Rightarrow> t''"  and "s\<^sub>2 = t'' (\<le> l)"
    using WhileTrue.IH(1) WhileTrue.prems(2) \<open>0 \<turnstile> c\<close> by blast
  obtain t' where t' : "(?w, t'') \<Rightarrow> t'" and "s\<^sub>3 = t'(\<le> l)" 
    by (meson WhileTrue.IH(2) WhileTrue.prems(1) \<open>s\<^sub>2 = t'' (\<le> l)\<close>)
  have "bval b t" 
    using WhileTrue.hyps(1) WhileTrue.prems(2) bval_eq_if_eq_le by auto
  then show ?case 
    using \<open>s\<^sub>3 = t' (\<le> l)\<close> t' t'' by blast
qed


subsubsection "The Standard System"

text\<open>The predicate \<^prop>\<open>l \<turnstile> c\<close> is nicely intuitive and executable. The
standard formulation, however, is slightly different, replacing the maximum
computation by an antimonotonicity rule. We introduce the standard system now
and show the equivalence with our formulation.\<close>

inductive sec_type' :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile>'' _)" [0,0] 50) where
Skip':
  "l \<turnstile>' SKIP"  |
Assign':
  "\<lbrakk> sec x \<ge> sec a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile>' x ::= a"  |
Seq':
  "l \<turnstile>' c\<^sub>1 \<Longrightarrow> l \<turnstile>' c\<^sub>2 \<Longrightarrow> l \<turnstile>' c\<^sub>1;;c\<^sub>2"  |
If':
  "\<lbrakk> sec b \<le> l;  l \<turnstile>' c\<^sub>1;  l \<turnstile>' c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2"  |
While':
  "\<lbrakk> sec b = 0;  0 \<turnstile>' c \<rbrakk> \<Longrightarrow> 0 \<turnstile>' WHILE b DO c"  |
anti_mono':
  "\<lbrakk> l \<turnstile>' c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile>' c"

(* Lemma 9.23 (Equivalence to standard formulation). *)
lemma sec_type_sec_type': 
  "l \<turnstile> c \<Longrightarrow> l \<turnstile>' c"
  apply (induction rule: sec_type.induct)
  apply (simp add: Skip')
     apply (simp add: Assign')
    apply (simp add: Seq')
   apply (meson If' anti_mono' max.cobounded1 max.cobounded2)
  by (simp add: While')

lemma sec_type'_sec_type:
  "l \<turnstile>' c \<Longrightarrow> l \<turnstile> c"
  apply (induction rule: sec_type'.induct)
  apply (simp add: Skip)
     apply (simp add: Assign)
    apply (simp add: Seq)
  apply (simp add: If max_def)
   apply (simp add: While)
  using anti_mono by blast

corollary sec_type_eq: "l \<turnstile> c \<longleftrightarrow> l \<turnstile>' c"
  using sec_type'_sec_type sec_type_sec_type' by blast

end