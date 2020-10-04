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
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  show ?case 
    proof cases
      assume "sec b \<le> l"
      then have "s = t (\<le> sec b)" 
        using IfTrue.prems(3) \<open>sec b \<le> l\<close> by auto
      hence "bval b t" 
        using IfTrue.hyps(1) bval_eq_if_eq_le by blast
      with IfTrue.IH IfTrue.prems(1,3) \<open>sec b \<turnstile> c\<^sub>1\<close> anti_mono
      show ?thesis by (auto)
    next
      assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" 
        by (simp add: If \<open>sec b \<turnstile> c\<^sub>1\<close> \<open>sec b \<turnstile> c\<^sub>2\<close>)
      then have "t = t' (\<le> l)" 
        using IfTrue.prems(1) \<open>\<not> sec b \<le> l\<close> confinement by auto
      then show ?thesis 
        using IfTrue.hyps(2) IfTrue.prems(3) \<open>\<not> sec b \<le> l\<close> \<open>sec b \<turnstile> c\<^sub>1\<close> confinement by fastforce
    qed
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  show ?case 
    proof cases
      assume "sec b \<le> l"
      then have "s = t (\<le> sec b)" 
        using IfFalse.prems(3) le_trans by blast
      hence "\<not>bval b t" 
        using IfFalse.hyps(1) bval_eq_if_eq_le by auto
      with IfFalse.IH IfFalse.prems(1,3) \<open>sec b \<turnstile> c\<^sub>2\<close> anti_mono
      show ?thesis by blast
    next
      assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" 
        by (simp add: If \<open>sec b \<turnstile> c\<^sub>1\<close> \<open>sec b \<turnstile> c\<^sub>2\<close>)
      then have "t = t' (\<le> l)" 
        using IfFalse.prems(1) \<open>\<not> sec b \<le> l\<close> confinement by auto
      then show ?thesis 
        using IfFalse.hyps(2) IfFalse.prems(3) \<open>\<not> sec b \<le> l\<close> \<open>sec b \<turnstile> c\<^sub>2\<close> confinement by fastforce
    qed
next
  case (WhileFalse b s c)
  have "sec b \<turnstile> c" 
    using WhileFalse.prems(2) com.distinct(17) com.distinct(19) com.distinct(7) by force
  show ?case 
  proof cases
    assume "sec b \<le> l"
      then have "s = t (\<le> sec b)" 
        using WhileFalse.prems(3) dual_order.trans by blast
      hence "\<not>bval b t" 
        using WhileFalse.hyps bval_eq_if_eq_le by blast
    then show ?thesis 
      using WhileFalse.prems(1) WhileFalse.prems(3) by blast
  next
    assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> WHILE b DO c" 
        by (simp add: While \<open>sec b \<turnstile> c\<close>)
      then have "t = t' (\<le> l)" 
        using WhileFalse.prems(1) \<open>\<not> sec b \<le> l\<close> confinement by auto
    then show ?thesis 
      by (simp add: WhileFalse.prems(3))
  qed
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3 t1 t3)
  have "sec b \<turnstile> c" 
    using WhileTrue.prems(2) by force
  show ?case 
    proof cases
      assume "sec b \<le> l"
      then have "s\<^sub>1 = t1 (\<le> sec b)" 
        using WhileTrue.prems(3) \<open>sec b \<le> l\<close> by auto
      hence "bval b t1" 
        using WhileTrue.hyps(1) bval_eq_if_eq_le by blast
      then obtain t2 where "(c, t1) \<Rightarrow> t2" "(WHILE b DO c , t2 ) \<Rightarrow> t3" 
        using WhileTrue.prems(1) by auto
      with WhileTrue.IH(1,2) WhileTrue.prems(2, 3) anti_mono
      show ?thesis by auto
    next
      assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> WHILE b DO c" 
        by (simp add: While \<open>sec b \<turnstile> c\<close>)
      then have "t1 = t3 (\<le> l)" 
        using WhileTrue.prems(1) \<open>\<not> sec b \<le> l\<close> confinement max_absorb1 by auto
      with WhileTrue.hyps(2,3) WhileTrue.prems(3) \<open>\<not> sec b \<le> l\<close> \<open>sec b \<turnstile> WHILE b DO c\<close> \<open>sec b \<turnstile> c\<close> 
      show ?thesis 
        by (smt confinement dual_order.strict_trans not_le_imp_less order.not_eq_order_implies_strict)
    qed
  qed

subsubsection "The Standard Typing System"

text\<open>The predicate \<^prop>\<open>l \<turnstile> c\<close> is nicely intuitive and executable. The
standard formulation, however, is slightly different, replacing the maximum
computation by an antimonotonicity rule. We introduce the standard system now
and show the equivalence with our formulation.\<close>

inductive sec_type' :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile>'' _)" [0,0] 50) where
Skip':
  "l \<turnstile>' SKIP" |
Assign':
  "\<lbrakk> sec x \<ge> sec a; sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile>' x ::= a" |
Seq':
  "\<lbrakk> l \<turnstile>' c\<^sub>1;  l \<turnstile>' c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' c\<^sub>1;;c\<^sub>2" |
If':
  "\<lbrakk> sec b \<le> l;  l \<turnstile>' c\<^sub>1;  l \<turnstile>' c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2" |
While':
  "\<lbrakk> sec b \<le> l;  l \<turnstile>' c \<rbrakk> \<Longrightarrow> l \<turnstile>' WHILE b DO c" |
anti_mono':
  "\<lbrakk> l \<turnstile>' c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile>' c"


(* Lemma 9.15 *)
lemma sec_type_sec_type': "l \<turnstile> c \<Longrightarrow> l \<turnstile>' c"
  apply(induction rule: sec_type.induct)
      apply (simp add: Skip')
     apply(simp add: Assign')
    apply(simp add: Seq')
(*   apply (smt max.cobounded1 max.cobounded2 sec_type'.simps)*)
   apply (metis max.commute max.absorb_iff2 nat_le_linear If' anti_mono')
  by (metis While' anti_mono' le_cases max.absorb_iff2 max.order_iff)


(* Lemma 9.16 *)
lemma sec_type'_sec_type: "l \<turnstile>' c \<Longrightarrow> l \<turnstile> c"
  apply(induction rule: sec_type'.induct)
       apply(simp add: Skip)
  apply(simp add: Assign)
     apply(simp add: Seq)
    apply (simp add: If max.absorb2)
   apply (simp add: While max_def)
  using anti_mono by blast


subsubsection "A Bottom-Up Typing System"

inductive sec_type2 :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile> _ : _)" [0,0] 50) where
Skip2:
  "\<turnstile> SKIP : l" |
Assign2:
  "sec x \<ge> sec a \<Longrightarrow> \<turnstile> x ::= a : sec x" |
Seq2:
  "\<lbrakk> \<turnstile> c\<^sub>1 : l\<^sub>1;  \<turnstile> c\<^sub>2 : l\<^sub>2 \<rbrakk> \<Longrightarrow> \<turnstile> c\<^sub>1;;c\<^sub>2 : min l\<^sub>1 l\<^sub>2 " |
If2:
  "\<lbrakk> sec b \<le> min l\<^sub>1 l\<^sub>2;  \<turnstile> c\<^sub>1 : l\<^sub>1;  \<turnstile> c\<^sub>2 : l\<^sub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 : min l\<^sub>1 l\<^sub>2" |
While2:
  "\<lbrakk> sec b \<le> l;  \<turnstile> c : l \<rbrakk> \<Longrightarrow> \<turnstile> WHILE b DO c : l"


(* Lemma 9.17 *)
lemma sec_type2_sec_type': "\<turnstile> c : l \<Longrightarrow> l \<turnstile>' c"
  apply(induction rule: sec_type2.induct)
      apply(simp add: Skip')
     apply(simp add: Assign')
    apply (meson Seq' anti_mono' min.cobounded1 min.cobounded2)
  apply (metis If' anti_mono' le_cases min_def)
  by (simp add: While')

(* Lemma 9.18 *)
lemma sec_type'_sec_type2: "l \<turnstile>' c \<Longrightarrow> \<exists> l' \<ge> l. \<turnstile> c : l'"
  apply(induction rule: sec_type'.induct)
       apply(simp add: Skip2)
       apply(auto)
  using Assign2 apply blast
  using Seq2 min.bounded_iff apply blast
    apply (metis (no_types, hide_lams) If2 le_trans min.bounded_iff)
  using While2 le_trans apply blast
  using le_trans by blast

(* Exercise 9.5 *)
fun ok :: "level \<Rightarrow> com \<Rightarrow> bool"  where
"ok l SKIP = True" |
"ok l (x ::= a) = ((sec x \<ge> sec a) \<and> (sec x \<ge> l))" |
"ok l (c1;;c2) = ((ok l c1) \<and> (ok l c2))" |
"ok l (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = ((ok (max (sec b) l) c\<^sub>1) \<and> (ok ( max (sec b) l) c\<^sub>2))" |
"ok l (WHILE b DO c) = ok (max (sec b) l) c"

lemma ok_sec_type: "ok l c \<Longrightarrow> l \<turnstile> c"
  apply(induction rule: ok.induct)
  using sec_type.Skip apply blast
  using sec_type.Assign apply auto
    apply (simp add: sec_type.Seq)
   apply (simp add: If)
  using While by blast

lemma sec_type_ok: "l \<turnstile> c \<Longrightarrow> ok l c"
  apply(induction rule: sec_type.induct)
      apply(simp add: Skip)
     apply(simp add: Assign)
    apply simp
   apply simp
  apply(simp)
  done

theorem "(l \<turnstile> c) = ok l c"
  using ok_sec_type sec_type_ok by blast

(* 
Skip':
  "l \<turnstile>' SKIP" |
Assign':
  "\<lbrakk> sec x \<ge> sec a; sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile>' x ::= a" |
Seq':
  "\<lbrakk> l \<turnstile>' c\<^sub>1;  l \<turnstile>' c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' c\<^sub>1;;c\<^sub>2" |
If':
  "\<lbrakk> sec b \<le> l;  l \<turnstile>' c\<^sub>1;  l \<turnstile>' c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2" |
While':
  "\<lbrakk> sec b \<le> l;  l \<turnstile>' c \<rbrakk> \<Longrightarrow> l \<turnstile>' WHILE b DO c" |
anti_mono':
  "\<lbrakk> l \<turnstile>' c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile>' c"

fun ok' :: "level \<Rightarrow> com \<Rightarrow> bool"  where
"ok' l SKIP = True" |
"ok' l (x ::= a) = ((sec x \<ge> sec a) \<and> (sec x \<ge> l))" |
"ok' l (c1;;c2) = ((ok' l c1) \<and> (ok' l c2))" |
"ok' l (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = ((sec b \<le> l)\<and> (ok l c\<^sub>1) \<and> (ok l c\<^sub>2))" |
"ok' l (WHILE b DO c) = (sec b \<le> l \<and> ok l c)" |
"ok' l' c = (\<exists>l. (ok' l c \<and> l' \<le> l))" <- It is difficult to reformulate this case.
*)

(* Exercise 9.6*)

inductive sec_type2' :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile>'' _ : _)" [0,0] 50) where
Skip2':
  "\<turnstile>' SKIP : l" |
Assign2':
  "sec x \<ge> sec a \<Longrightarrow> \<turnstile>' x ::= a : sec x" |
Seq2':
  "\<lbrakk> \<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l \<rbrakk> \<Longrightarrow> \<turnstile>' c\<^sub>1;;c\<^sub>2 : l " |
If2':
  "\<lbrakk> sec b \<le> l;  \<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l \<rbrakk>
  \<Longrightarrow> \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2 : l" |
While2':
  "\<lbrakk> sec b \<le> l;  \<turnstile>' c : l \<rbrakk> \<Longrightarrow> \<turnstile>' WHILE b DO c : l"|
Subsumption2':
  "\<lbrakk>\<turnstile>' c:l ; l' \<le> l\<rbrakk> \<Longrightarrow> \<turnstile>' c : l'"

lemma "\<turnstile>' c : l \<Longrightarrow> \<exists> l' \<ge> l. \<turnstile> c : l'"
    apply(induction rule: sec_type2'.induct)
  apply (metis Skip2 less_or_eq_imp_le)
      apply (metis Assign2 less_or_eq_imp_le)
  
  apply (metis (full_types) Seq' anti_mono' sec_type'_sec_type2 sec_type2_sec_type')

  apply (metis If' anti_mono' sec_type'_sec_type2 sec_type2_sec_type')
  apply (metis While2 le_trans)
  apply (metis le_trans)
  done
(*    apply (meson Seq2' Subsumption min.cobounded1 min.cobounded2)*)

lemma "\<turnstile> c : l \<Longrightarrow> \<turnstile>' c : l" 
proof (induct rule: sec_type2.induct)
  case Seq2
  thus ?case
    by (meson Seq2' Subsumption2' min.cobounded1 min.cobounded2)

next
  case If2
  thus ?case
    by (metis If2' Subsumption2' min.bounded_iff nat_le_linear)
qed (auto intro: sec_type2'.intros)


(* Exercise 9.7. *)
fun erase :: "level \<Rightarrow> com \<Rightarrow> com" where
  "erase l (SKIP) = SKIP"
  |"erase l (x ::= a) = (if (sec x \<ge> l) then SKIP else x ::= a)"
  | "erase l (Seq com1 com2) = Seq (erase l com1) (erase l com2)"
  | "erase l (If bexp com1 com2) = (if (sec bexp \<ge> l) then SKIP else (If bexp (erase l com1) (erase l com2)))"
  |"erase l (While  bexp com) = (if sec bexp \<ge> l then SKIP else (While bexp (erase l com)))"


(*
  "\<lbrakk> (c,s) \<Rightarrow> s'; (c,t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (\<le> l) \<rbrakk>
   \<Longrightarrow> s' = t' (\<le> l)"
*)
lemma "\<lbrakk>(c, s) \<Rightarrow> s'; (erase l c, t) \<Rightarrow> t'; 0 \<turnstile> c; s = t (< l)\<rbrakk>
       \<Longrightarrow> s' = t' (< l)"
  sorry
(*proof(induction arbitrary: t t' rule: big_step_induct)
case (Skip s)
  then show ?case by auto
next
  case (Assign x a s)
  have [simp]:"t' = t(x := aval a t)" using Assign sorry
  have "sec a \<le> sec x"  using \<open>0 \<turnstile> x ::= a\<close> by auto
  show ?case 
  proof auto
(* 1. sec x \<le> l \<Longrightarrow> aval a s = aval a t
 2. \<And>xa. xa \<noteq> x \<Longrightarrow> sec xa \<le> l \<Longrightarrow> s xa = t xa*)
    assume " sec x < l"
    have "sec a < l" 
      using \<open>sec a \<le> sec x\<close> \<open>sec x < l\<close> by linarith
    thus " aval a s = aval a t" 
      using Assign.prems(3) aval_eq_if_eq_le dual_order.strict_trans2 by blast
  next
    fix xa assume "xa \<noteq> x" "sec xa < l"
    thus "s xa = t xa" 
      by (simp add: Assign.prems(3))
  qed
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by blast
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  show ?case 
    proof cases
      assume "sec b \<le> l"
      then have "s = t (\<le> sec b)" 
        using IfTrue.prems(3) \<open>sec b \<le> l\<close> by auto
      hence "bval b t" 
        using IfTrue.hyps(1) bval_eq_if_eq_le by blast
      with IfTrue.IH IfTrue.prems(1,3) \<open>sec b \<turnstile> c\<^sub>1\<close> anti_mono
      show ?thesis by (auto)
    next
      assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" 
        by (simp add: If \<open>sec b \<turnstile> c\<^sub>1\<close> \<open>sec b \<turnstile> c\<^sub>2\<close>)
      then have "t = t' (\<le> l)" 
        using IfTrue.prems(1) \<open>\<not> sec b \<le> l\<close> confinement by auto
      then show ?thesis 
        using IfTrue.hyps(2) IfTrue.prems(3) \<open>\<not> sec b \<le> l\<close> \<open>sec b \<turnstile> c\<^sub>1\<close> confinement by fastforce
    qed
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  show ?case 
    proof cases
      assume "sec b \<le> l"
      then have "s = t (\<le> sec b)" 
        using IfFalse.prems(3) le_trans by blast
      hence "\<not>bval b t" 
        using IfFalse.hyps(1) bval_eq_if_eq_le by auto
      with IfFalse.IH IfFalse.prems(1,3) \<open>sec b \<turnstile> c\<^sub>2\<close> anti_mono
      show ?thesis by blast
    next
      assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" 
        by (simp add: If \<open>sec b \<turnstile> c\<^sub>1\<close> \<open>sec b \<turnstile> c\<^sub>2\<close>)
      then have "t = t' (\<le> l)" 
        using IfFalse.prems(1) \<open>\<not> sec b \<le> l\<close> confinement by auto
      then show ?thesis 
        using IfFalse.hyps(2) IfFalse.prems(3) \<open>\<not> sec b \<le> l\<close> \<open>sec b \<turnstile> c\<^sub>2\<close> confinement by fastforce
    qed
next
  case (WhileFalse b s c)
  have "sec b \<turnstile> c" 
    using WhileFalse.prems(2) com.distinct(17) com.distinct(19) com.distinct(7) by force
  show ?case 
  proof cases
    assume "sec b \<le> l"
      then have "s = t (\<le> sec b)" 
        using WhileFalse.prems(3) dual_order.trans by blast
      hence "\<not>bval b t" 
        using WhileFalse.hyps bval_eq_if_eq_le by blast
    then show ?thesis 
      using WhileFalse.prems(1) WhileFalse.prems(3) by blast
  next
    assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> WHILE b DO c" 
        by (simp add: While \<open>sec b \<turnstile> c\<close>)
      then have "t = t' (\<le> l)" 
        using WhileFalse.prems(1) \<open>\<not> sec b \<le> l\<close> confinement by auto
    then show ?thesis 
      by (simp add: WhileFalse.prems(3))
  qed
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3 t1 t3)
  have "sec b \<turnstile> c" 
    using WhileTrue.prems(2) by force
  show ?case 
    proof cases
      assume "sec b \<le> l"
      then have "s\<^sub>1 = t1 (\<le> sec b)" 
        using WhileTrue.prems(3) \<open>sec b \<le> l\<close> by auto
      hence "bval b t1" 
        using WhileTrue.hyps(1) bval_eq_if_eq_le by blast
      then obtain t2 where "(c, t1) \<Rightarrow> t2" "(WHILE b DO c , t2 ) \<Rightarrow> t3" 
        using WhileTrue.prems(1) by auto
      with WhileTrue.IH(1,2) WhileTrue.prems(2, 3) anti_mono
      show ?thesis by auto
    next
      assume "\<not> sec b \<le> l"
      have "sec b \<turnstile> WHILE b DO c" 
        by (simp add: While \<open>sec b \<turnstile> c\<close>)
      then have "t1 = t3 (\<le> l)" 
        using WhileTrue.prems(1) \<open>\<not> sec b \<le> l\<close> confinement max_absorb1 by auto
      with WhileTrue.hyps(2,3) WhileTrue.prems(3) \<open>\<not> sec b \<le> l\<close> \<open>sec b \<turnstile> WHILE b DO c\<close> \<open>sec b \<turnstile> c\<close> 
      show ?thesis 
        by (smt confinement dual_order.strict_trans not_le_imp_less order.not_eq_order_implies_strict)
    qed
  qed
*)
end