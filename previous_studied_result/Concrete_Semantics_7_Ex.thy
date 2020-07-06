theory Concrete_Semantics_7_Ex
  imports Main "~~/src/HOL/IMP/Com" "HOL-IMP.Big_Step" "HOL-IMP.Small_Step"
begin

(* Exercise 7.1. *)

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (v ::= va) = {v}"| 
"assigned (v;; va) = assigned v \<union> assigned va " |
"assigned (IF v THEN va ELSE vb) = assigned va \<union> assigned vb" | 
"assigned (WHILE v DO va) = assigned va"

lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
proof(induction rule:big_step_induct)
  case (Skip s)
  then show ?case 
    by simp
next
  case (Assign x a s)
  then show ?case 
    by simp
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case 
    by simp
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case by simp
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case by simp
next
  case (WhileFalse b s c)
  then show ?case by simp
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case by simp
qed

(* Exercise 7.2. *)
fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True" |
"skip (v ::= va) = False" |
"skip (v;; va) = (skip v \<and> skip va)" |
"skip (IF v THEN va ELSE vb) = (skip va \<and> skip vb)" |
"skip (WHILE v DO va) = False"

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
proof(induction c)
case SKIP
  then show ?case 
    by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  then show ?case 
    by fastforce
next
  case (If x1 c1 c2)
  then show ?case 
    by (meson Big_Step.IfE big_step.IfFalse big_step.IfTrue skip.simps(4))
next
  case (While x1 c)
  then show ?case 
    by simp
qed

(* Exercise 7.3. *)
fun deskip :: "com \<Rightarrow> com" where
"deskip SKIP = SKIP" |
(* b is aexp so not to do deskip*)
"deskip (a ::= b) = a ::= b" |
"deskip (a;; b) = (if deskip a = SKIP then deskip b else 
  (if deskip b = SKIP then deskip a 
    else deskip a;; deskip b))" |
"deskip (IF a THEN b ELSE c) = IF a THEN deskip b ELSE deskip c" |
"deskip (WHILE a DO b) = WHILE a DO deskip b"

value "deskip (SKIP;; WHILE b DO (x ::= a;; SKIP))"

lemma "deskip c \<sim> c"
proof(induction c)
case SKIP
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  then have "(c1 ;; c2) \<sim> (deskip c1;; deskip c2)" 
    by blast
  moreover have " deskip (c1;; c2) \<sim> (deskip c1;; deskip c2)" 
    by auto
(* deskip (c1;; c2) \sim (deskip c1;; deskip c2) \sim (c1;; c2) *)
  ultimately show ?case by auto
next
  case (If x1 c1 c2)
  then show ?case 
    by auto
next
  case (While x1 c)

  then show ?case 
    using sim_while_cong by auto
qed

inductive astep :: "aexp * state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x , s) \<leadsto>  N (s x )" |
"(Plus (N i) (N j ), s) \<leadsto> N (i + j )" |
"(x2, s) \<leadsto> a2 \<Longrightarrow> (Plus x1 x2, s) \<leadsto> Plus x1 a2" |
"(x1, s) \<leadsto> a1 \<Longrightarrow> (Plus x1 (N j), s) \<leadsto> Plus a1 (N j)"


lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep.induct[split_format(complete)])
  fix x s 
  show "aval (V x) s = aval (N (s x)) s" 
    by simp

  fix i j s
  show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" 
    by simp

  fix x2 s a2 x1
  assume "aval x2 s = aval a2 s"
  then show "aval (Plus x1 x2) s = aval (Plus x1 a2) s" 
    by simp

  fix x1 s a1 j
  assume "aval x1 s = aval a1 s"
  then show "aval (Plus x1 (N j)) s = aval (Plus a1 (N j)) s" 
    by simp 
qed

lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim>
IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"(is "?left \<sim> ?right")
proof -
  have "(?left,s) \<Rightarrow> t \<Longrightarrow> (?right, s) \<Rightarrow> t"  for s t
  proof -
    assume "(?left, s) \<Rightarrow> t"
    show "(?right, s) \<Rightarrow> t" 
      using IfTrue \<open>(IF And b1 b2 THEN c1 ELSE c2, s) \<Rightarrow> t\<close> by fastforce
  qed
  moreover have "(?right, s) \<Rightarrow> t \<Longrightarrow> (?left,s) \<Rightarrow> t"  for s t
  proof -
    assume "(?right, s) \<Rightarrow> t" 
    show "(?left, s) \<Rightarrow> t" 
      using \<open>(IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2, s) \<Rightarrow> t\<close> by auto
  qed
  ultimately show ?thesis 
    by blast 
qed
  
(* obviously false*)

(* 
  then show False by (induction rule: big_step_induct)
Failed to finish proof\<^here>:
goal (3 subgoals):
 1. \<And>s. False
 2. \<And>x a s. False
 3. \<And>b s c. \<not> bval b s \<Longrightarrow> False

  then show False by (induction "WHILE (Bc True) DO WHILE (Bc False) DO SKIP" s s rule: big_step_induct)
Failed to finish proof\<^here>:
goal (1 subgoal):
 1. \<And>s. \<not> bval (Bc True) s \<Longrightarrow> False
 *)
lemma "\<not> (\<forall> b1 b2 c. WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)"(is "\<not> ?p")
proof 
  assume assm: ?p
  have 1: "WHILE And (Bc True) (Bc False) DO SKIP \<sim> WHILE (Bc True) DO WHILE (Bc False) DO SKIP"
    using assm by simp
  have 2: "(WHILE And (Bc True) (Bc False) DO SKIP, s) \<Rightarrow> s" by auto
  have 3: "(WHILE (Bc True) DO WHILE (Bc False) DO SKIP, s) \<Rightarrow> s" 
    using "2" assm by auto
  then show False 
    by (induction "WHILE (Bc True) DO WHILE (Bc False) DO SKIP" s s rule: big_step_induct, simp)
qed

lemma temination_of_while: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not> bval b t"
  apply(induction "WHILE b DO c" s t rule: big_step_induct )
   apply simp
  by simp


  
(*
It is easy to show there is a proof of left to right.
However, it is difficult to construct proof.
The following method is failed to calculate:
    assume assm: "(?left, s) \<Rightarrow> t"
    then show "(?left;;?q, s) \<Rightarrow> t"
      by (induction "WHILE Or b1 b2 DO c" s t rule: big_step_induct)
.
*)
lemma "WHILE Not (And (Not b1) (Not b2)) DO c \<sim> WHILE Not (And (Not b1) (Not b2)) DO c;; WHILE b1 DO c"(is "?left \<sim> ?left;;?q")
proof -
  have "(?left,s) \<Rightarrow> t \<Longrightarrow> (?left;;?q, s) \<Rightarrow> t"  for s t
  proof -
    assume assm: "(?left, s) \<Rightarrow> t"
    show "(?left;;?q, s) \<Rightarrow> t"
      using Seq WhileFalse assm temination_of_while by fastforce
  qed
  moreover have "(?left;;?q, s) \<Rightarrow> t \<Longrightarrow> (?left,s) \<Rightarrow> t"  for s t
  proof -
    assume "(?left;;?q, s) \<Rightarrow> t" 
    show "(?left, s) \<Rightarrow> t"
      by (metis SeqE \<open>(WHILE bexp.Not (And (bexp.Not b1) (bexp.Not b2)) DO c;; WHILE b1 DO c, s) \<Rightarrow> t\<close> big_step_determ calculation)
  qed
  ultimately show ?thesis 
    by blast 
qed

(* Exercise 7.6. *)
definition Do :: "com \<Rightarrow> bexp \<Rightarrow> com" ("DO _ WHILE _"  [0, 61] 61) where
"DO c WHILE b = c ;; WHILE b DO c" 

fun dewhile :: "com \<Rightarrow> com" where
"dewhile SKIP = SKIP" |
(* b is aexp so not to do deskip*)
"dewhile (a ::= b) = a ::= b" |
"dewhile (a;; b) = (dewhile a;; dewhile b)" |
"dewhile (IF a THEN b ELSE c) = IF a THEN dewhile b ELSE dewhile c" |
"dewhile (WHILE a DO b) = IF a THEN (DO dewhile b WHILE a) ELSE SKIP "

lemma "dewhile c \<sim> c"(is "?left \<sim> ?right")
proof (induction c)
  case SKIP
then show ?case 
  by simp
next
  case (Assign x1 x2)
  then show ?case 
    by simp
next
  case (Seq c1 c2)
  then show ?case 
    by auto
next
  case (If x1 c1 c2)
  then show ?case 
    by auto
next
  case (While x1 c)
  then show ?case 
    using Do_def sim_while_cong while_unfold by auto
qed

(* Exercise 7.7. *)

lemma assumes "C 0 = c;; d" 
  and "\<forall>n. (C n, S n) \<rightarrow> (C (Suc n), S (Suc n))"
  shows "(\<forall> n.  \<exists>c1 c2.
      C n = c1;; d \<and>
      C (Suc n) = c2;; d \<and> (c1, S n) \<rightarrow> (c2, S (Suc n))) \<or>
      (\<exists> k. C k = SKIP;; d)"(is "(?P) \<or> ?Q")
proof cases
  assume "?Q"
  then show ?thesis 
    by simp
next
  assume "\<not> ?Q"
  {fix i
    have "\<exists>c1 c2.
        C i = c1;; d \<and>
        C (Suc i) = c2;; d \<and> 
        (c1, S i) \<rightarrow> (c2, S (Suc i))" 
    proof (induction i)
      case 0
      then show ?case 
        by (metis Pair_inject Small_Step.SeqE \<open>\<nexists>k. C k = SKIP;; d\<close> assms(1) assms(2))
    next
      case (Suc i)
      then show ?case 
        by (metis Pair_inject Small_Step.SeqE \<open>\<nexists>k. C k = SKIP;; d\<close> assms(2))
    qed}
    then have ?P 
      by auto
  then show ?thesis by simp
qed

(*

  assume "\<not> ?P"
  then obtain n where
    "\<forall> c1 c2. C n \<noteq> c1;; d \<or> 
    C (Suc n) \<noteq> c2;; d \<or>
    \<not> ((c1, S n) \<rightarrow> (c2, S (Suc n)))" 
    by auto

To show ?thesis, I want the case 
- "c2 = SKIP" and 
- "C (Suc n) = c2;; d"
, so, it is needed to show that 
- "C n \<noteq> c1;; d"
? ? ? ?
CRAZY.
REMIND.
*)



end