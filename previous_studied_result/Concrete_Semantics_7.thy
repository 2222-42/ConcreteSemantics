theory Concrete_Semantics_7
  imports Main "~~/src/HOL/IMP/Com" "HOL-IMP.Star"
begin

(* "~~/src/HOL/IMP/Com" *)
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

schematic_goal ex : "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
  apply(rule Seq)
   apply(rule Assign)
  apply simp
  apply(rule Assign)
  done
thm ex[simplified]

code_pred big_step .

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"
values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"
values "{map t [''x'', ''y''] |t. (''x'' ::= N 2, \<lambda>_.0) \<Rightarrow> t}"

(* the following inverted rules(inductive cases) are needed to prove. *)
inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm SkipE
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE

declare big_step.intros [intro]
thm big_step.induct

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
  by blast

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
  shows "t = s"
proof-
  from assms show ?thesis
  proof cases
  case IfTrue
  then show ?thesis 
    by auto
next
  case IfFalse
  then show ?thesis  by blast
qed
qed

lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
c1: "(c1, s) \<Rightarrow> s1" and
c2: "(c2, s1) \<Rightarrow> s2" and
c3: "(c3, s2) \<Rightarrow> s'" 
    by blast
    from c2 c3 have "(c2;; c3, s1) \<Rightarrow> s'" 
      using Seq by auto
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" 
    using Seq \<open>(c2;; c3, s1) \<Rightarrow> s'\<close> c1 by blast
next
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"

  then show  "(c1;; c2;; c3, s) \<Rightarrow> s'" 
    by (meson Seq SeqE)
qed

abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
  by blast

lemma unfold_while:
  "(WHILE b DO c)\<sim>(IF b THEN c;; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
  have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases
      case WhileFalse
      then show ?thesis 
        by (simp add: IfFalse Skip)
    next
      case (WhileTrue s\<^sub>2)
      then show ?thesis 
        using IfTrue Seq by auto
    qed
  qed
  moreover 
  have  "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases
      case IfTrue
      then show ?thesis 
        using WhileTrue by auto
    next
      case IfFalse
      then show ?thesis 
        using WhileFalse by blast
    qed
  qed
  ultimately
  show ?thesis 
    by blast
qed

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
  by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
  by blast


(* Q. What is big_step.induct[split_format(complete)]?
A. The proof of Lemma 7.6
requires the advanced form of rule induction described in Section 5.4.6 because
the big-step premise in the lemma involves not just variables but the
proper term WHILE b DO c.
 *)
lemma sim_while_cong_aux:
  "\<lbrakk>(WHILE b DO c,s) \<Rightarrow> t ; c \<sim> c'\<rbrakk> \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
  apply(induction "WHILE b DO c" s t arbitrary: b c rule:  big_step.induct[split_format(complete)])
   apply (simp add: WhileFalse)
  by blast


lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  using sim_while_cong_aux by auto

lemma sim_refl:  "c \<sim> c" 
  by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" 
  by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" 
  by simp

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  apply(induction arbitrary:u rule: big_step.induct)
  apply (blast+)
  done

theorem "(c, s) \<Rightarrow> t \<Longrightarrow> (c, s) \<Rightarrow> t' \<Longrightarrow> t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  case (Skip s)
  then show ?case 
    by auto
next
  case (Assign x a s)
  then show ?case 
    by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case 
    by blast
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case 
    by blast
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case 
    by blast
next
  case (WhileFalse b s c)
  then show ?case 
    by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case 
    by blast
qed

