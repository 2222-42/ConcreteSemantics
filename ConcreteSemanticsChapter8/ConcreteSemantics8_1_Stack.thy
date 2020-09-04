theory ConcreteSemantics8_1_Stack
  imports Main "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Star"
begin

text \<open>

> Working with proofs on the machine language, we will find it convenient for the program counter to admit negative values, 
> The effect of this choice is that various decomposition lemmas about machine executions have nicer algebraic properties and fewer preconditions than their nat counterparts

  In the following, we use the length of lists as integers 
  instead of natural numbers. Instead of converting \<^typ>\<open>nat\<close>
  to \<^typ>\<open>int\<close> explicitly, we tell Isabelle to coerce \<^typ>\<open>nat\<close>
  automatically when necessary.
\<close>
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

text\<open>
Missing patterns in function definition:
\<And>b. [] !! b = undefined 
Found termination order: "(\<lambda>p. length (fst p)) <*mlex*> {}"
\<close>

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a"(infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

text\<open>
Type unification failed: Clash of types "nat" and "int"

Type error in application: incompatible operand type

Operator:  (<) i :: int \<Rightarrow> bool
Operand:   length xs :: nat

This problem is solved by set declare in top of this theory.
\<close>
lemma inth_append[simp]: "0 \<le> i \<Longrightarrow> (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
  apply(induction xs arbitrary: i)
  (* Unfortunately, the following method is not derived only by sledgehammer *)
   apply (auto simp add: algebra_simps)
  done

abbreviation (output)
  "isize xs == int (length xs)"

notation isize ("size")

datatype instr =
  LOADI int | LOAD vname | ADD | STORE vname |
  JMP int | JMPLESS int | JMPGE int

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs \<equiv> hd (tl xs)"
abbreviation "tl2 xs \<equiv> tl (tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
"iexec instr (i,s,stk) = (case instr of
  LOADI n \<Rightarrow> (i+1, s, n # stk) |
  LOAD x \<Rightarrow> (i +1, s, s x # stk) |
  ADD \<Rightarrow> (i+1, s, (hd2 stk + hd stk) # tl2 stk) |
  STORE x \<Rightarrow> (i + 1, s(x := hd stk), tl stk) |
  JMP n \<Rightarrow> (i + 1 + n, s, stk)| 
  JMPLESS n \<Rightarrow> (if hd2 stk < hd stk then i + 1 + n else i + 1, s, tl2 stk)| 
  JMPGE n \<Rightarrow>  (if hd stk \<le> hd2 stk then i + 1 + n else i + 1, s, tl2 stk)
)"

definition exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60)where
"P \<turnstile> c \<rightarrow> c' =
(\<exists>i s stk. c = (i,s,stk) \<and> c' = iexec(P!!i) (i,s,stk) \<and> 0 \<le> i \<and> i < size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size P
  \<Longrightarrow> P \<turnstile> (i,s,stk) \<rightarrow> c'"
  by (simp add: exec1_def)

abbreviation exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" [59,0,59] 60)where
"exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

text\<open>this code_pred are not proved by using `metis` without the above lemma "exec1I"\<close>
code_pred exec1 by (metis exec1_def)

text\<open>
Without `code_pred exec1`, Following values are not calculated by the following reason:
  No mode possible for comprehension
\<close>
values "{(i, map t [''x'', ''y''], stk ) | i t stk. [LOAD ''y'', STORE ''x''] \<turnstile> (0, <''x'' := 3, ''y'' := 4>, []) \<rightarrow>* (i, t, stk )}"

(*lemma 8.4*)
lemma iexec_shift [simp]: 
  "((n+i',s',stk') = iexec x (n+i,s,stk)) \<longleftrightarrow> ((i',s',stk') = iexec x (i,s,stk))"
  apply(auto split:instr.split)
  done
text \<open>The split modifier is the hint to auto to perform a case split whenever it sees
a case expression over instr. Thus we guide auto towards the case distinction we made in our proof above.\<close>

lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow> c'"
  apply(auto simp: exec1_def)
  done

(* lemma 8.2 *)
lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
  apply(induction rule: star.induct)
   apply simp
  by (meson exec1_appendR star.step)

lemma exec1_appendL:
  fixes i i' :: int 
  shows
  "P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk') \<Longrightarrow>
   P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk')"
  unfolding exec1_def
  by (auto simp del: iexec.simps)

(* lemma exec1_appendL_other: "P \<turnstile> (i, s, stk) \<rightarrow> (i', s', stk') \<Longrightarrow>
P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow> (size P' + i', s', stk')"
  apply(auto simp: exec1_def) 
  sledgehammer
 *)

(* Lemma 8.3 *)
lemma exec_appendL: "P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk') \<Longrightarrow>
P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow>* (size P' + i', s', stk')"
  apply(induction rule: exec_induct)
   apply simp
  by (meson exec1_appendL star.simps)

(*this lemma is needed to prove the IfFalse part of lemma 8.9*)
lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0,s,stk) \<rightarrow>* (j,t,stk') \<Longrightarrow>
  instr#P \<turnstile> (1,s,stk) \<rightarrow>* (1+j,t,stk')"
by (drule exec_appendL[where P'="[instr]"]) simp

lemma exec_appendL_if[intro]:
  fixes i i' j :: int
  shows
  "size P' <= i
   \<Longrightarrow> P \<turnstile> (i - size P',s,stk) \<rightarrow>* (j,s',stk')
   \<Longrightarrow> i' = size P' + j
   \<Longrightarrow> P' @ P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')"
by (drule exec_appendL[where P'=P']) simp

(* Lemma 8.5 *)
text\<open>The text-book did not write `j''=size P + i'` in the following lemma.
This lack affects the proof of lemma 8.5.
\<close>
lemma exec_append_trans[intro]:"\<lbrakk> 
P \<turnstile> (0,s,stk) \<rightarrow>* (i', s', stk'); 
size P \<le> i';
P' \<turnstile> (i' - size P, s', stk') \<rightarrow>* (i'', s'', stk'');
j'' = size P + i''
\<rbrakk>
 \<Longrightarrow> P @ P' \<turnstile>  (0, s,stk) \<rightarrow>* (j'', s'', stk'')"
  by (meson exec_appendL_if exec_appendR star_trans)

declare Let_def[simp]

subsubsection "8.3 Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"


(*Lemma 8.6*)

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>* (size(acomp a),s,aval a s#stk)"
  by (induction a arbitrary: stk) fastforce+

fun bcomp :: "bexp \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> instr list" where
"bcomp (Bc v) f n = (if v=f then [JMP n] else [])" |
"bcomp (Not b) f n = bcomp b (\<not>f) n" |
"bcomp (And b1 b2) f n =
 (let cb2 = bcomp b2 f n;
        m = if f then size cb2 else (size cb2)+n;
      cb1 = bcomp b1 False m
  in cb1 @ cb2)" |
"bcomp (Less a1 a2) f n =
 acomp a1 @ acomp a2 @ (if f then [JMPLESS n] else [JMPGE n])"

value "bcomp (And (Bc True) (Bc True)) False 3"
value "bcomp (And (Bc False) (Bc True)) True 3"
value "bcomp (And (Less (V ''x'') (V ''y'')) (Bc True)) False 3"
value
  "bcomp (And (Less (V ''x'') (V ''y'')) (Not(Less (V ''u'') (V ''v''))))
     False 3"

(* Lemma 8.8 *)
lemma bcomp_correct[intro]:  fixes n :: int
  shows"
0 \<le> n \<Longrightarrow>
bcomp b f n \<turnstile> (0, s, stk) \<rightarrow>* (size(bcomp b f n) + (if f = bval b s then n else 0), s, stk)
"
proof(induction b arbitrary: f n)
  case (Bc x)
  then show ?case by fastforce
next
  case (Not b)
(*  then show ?case 
    using bcomp.simps(2) bval.simps(2) by presburger*)
  from Not(1)[where f="~f"] Not(2) show ?case by fastforce
next
  case (And b1 b2)
  from And(1)[of "if f then size(bcomp b2 f n) else size(bcomp b2 f n) + n" "False"]
       And(2)[of n f] And(3)
  show ?case by fastforce
next
  case (Less x1a x2a)
  then show ?case by fastforce
qed

fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;;c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (WHILE b DO c) =
 (let cc = ccomp c; cb = bcomp b False (size cc + 1)
  in cb @ cc @ [JMP (-(size cb + size cc + 1))])"

value "ccomp
 (IF Less (V ''u'') (N 1) THEN ''u'' ::= Plus (V ''u'') (N 1)
  ELSE ''v'' ::= V ''u'')"

value "ccomp (WHILE Less (V ''u'') (N 1) DO (''u'' ::= Plus (V ''u'') (N 1)))"

subsection "8.4 Preservation of Semantics"

(* Lemma 8.9  *)
lemma ccomp_bigstep: "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size (ccomp c), t, stk)"
proof(induction arbitrary: stk rule: big_step_induct)
case (Skip s)
  then show ?case by (fastforce)
next
  case (Assign x a s)
  then show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  let ?cc1 = "ccomp c\<^sub>1" let ?cc2 = "ccomp c\<^sub>2"
  have "?cc1 @ ?cc2 \<turnstile> (0, s\<^sub>1, stk) \<rightarrow>* (size ?cc1, s\<^sub>2, stk)" 
    by (simp add: Seq.IH(1) exec_appendR)
  moreover have "?cc1 @ ?cc2 \<turnstile> (size ?cc1, s\<^sub>2, stk) \<rightarrow>* (size (?cc1 @ ?cc2), s\<^sub>3, stk)" using Seq.IH(2) by fastforce
(* ccomp (?c\<^sub>12;; ?c\<^sub>22) \<turnstile> (0, ?s\<^sub>12, ?stka2) \<rightarrow>* (size (ccomp (?c\<^sub>12;; ?c\<^sub>22)), ?s\<^sub>32, ?stka2)  *)
    ultimately show ?case 
      by (metis (no_types, lifting) ccomp.simps(3) star_trans)
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case by fastforce
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case by fastforce
next
  case (WhileFalse b s c)
  then show ?case by fastforce
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  let ?cw = "ccomp (WHILE b DO c)"
(*
    bval b s\<^sub>1
    (c, s\<^sub>1) \<Rightarrow> s\<^sub>2
    (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3
    ccomp c \<turnstile> (0, s\<^sub>1, ?stk) \<rightarrow>* (size (ccomp c), s\<^sub>2, ?stk)
    ccomp (WHILE b DO c) \<turnstile> (0, s\<^sub>2, ?stk) \<rightarrow>* (size (ccomp (WHILE b DO c)), s\<^sub>3, ?stk)

goal (1 subgoal):
 1. ccomp (WHILE b DO c) \<turnstile> (0, s\<^sub>1, stk) \<rightarrow>* (size (ccomp (WHILE b DO c)), s\<^sub>3, stk)
*)
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb,s1,stk)" using \<open>bval b s1\<close> by fastforce
  have "?cw \<turnstile> (size ?cb,s1,stk) \<rightarrow>* (size ?cb + size ?cc,s2,stk)" using WhileTrue.IH by fastforce
  moreover have "?cw \<turnstile> (size ?cb + size ?cc,s2,stk) \<rightarrow>* (0,s2,stk)" by fastforce
  moreover have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" 
    using WhileTrue.IH(2) by blast
  ultimately  show ?case 
    by (meson \<open>ccomp (WHILE b DO c) \<turnstile> (0, s1, stk) \<rightarrow>* (size (bcomp b False (size (ccomp c) + 1)), s1, stk)\<close> star_trans)
qed

text\<open>the other direction is difficult to solve.\<close>

text \<open>The possible successor PCs of an instruction at position \<^term>\<open>n\<close>\<close>
definition isuccs :: "instr \<Rightarrow> int \<Rightarrow> int set" where
"isuccs i n = (case i of
  JMP j \<Rightarrow> {n + 1 + j} |
  JMPLESS j \<Rightarrow> {n + 1 + j, n + 1} |
  JMPGE j \<Rightarrow> {n + 1 + j, n + 1} |
  _ \<Rightarrow> {n +1})"

text \<open>The possible successors PCs of an instruction list\<close>
definition succs :: "instr list \<Rightarrow> int \<Rightarrow> int set" where
"succs P n = {s. \<exists>i::int. 0 \<le> i \<and> i < size P \<and> s \<in> isuccs (P!!i) (n+i)}" 

text \<open>Possible exit PCs of a program\<close>
definition exits :: "instr list \<Rightarrow> int set" where
"exits P = succs P 0 - {0..< size P}"

primrec 
  exec_n :: "instr list \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool" 
  ("_/ \<turnstile> (_ \<rightarrow>^_/ _)" [65,0,1000,55] 55)
where 
  "P \<turnstile> c \<rightarrow>^0 c' = (c'=c)" |
  "P \<turnstile> c \<rightarrow>^(Suc n) c'' = (\<exists>c'. (P \<turnstile> c \<rightarrow> c') \<and> P \<turnstile> c' \<rightarrow>^n c'')"

lemma succs_empty [iff]: "succs [] n = {}"
  by (simp add: succs_def)

lemma succs_Cons:
  "succs (x#xs) n = isuccs x n \<union> succs xs (1+n)" (is "_ = ?x \<union> ?xs")
proof
(*
goal (2 subgoals):
 1. succs (x # xs) n \<subseteq> isuccs x n \<union> succs xs (1 + n)
 2. isuccs x n \<union> succs xs (1 + n) \<subseteq> succs (x # xs) n
*)
  let ?isuccs = "\<lambda>p P n i::int. 0 \<le> i \<and> i < size P \<and> p \<in> isuccs (P!!i) (n+i)"

  have "p \<in> ?x \<union> ?xs" if assm: "p \<in> succs (x#xs) n" for p
  proof -
    (* take i becasuse assumption cotains list*)
    from assm obtain i::int where isuccs: "?isuccs p (x#xs) n i" unfolding succs_def by auto
    show ?thesis
    proof cases
      assume "i = 0"
      with isuccs
      show ?thesis by fastforce
    next
      assume "i \<noteq> 0"
      with isuccs
      have "?isuccs p xs (n+1) (i -1)" by fastforce
      then have "p \<in> ?xs" unfolding succs_def by fastforce
      show ?thesis 
        by (simp add: \<open>p \<in> succs xs (1 + n)\<close>)
    qed
  qed
  thus "succs (x#xs) n \<subseteq> ?x \<union> ?xs" ..

  have "p \<in> succs (x#xs) n" if assm: "p \<in> ?x \<or> p \<in> ?xs" for p
  proof -
    from assm show ?thesis
    proof 
      assume "p \<in> ?x" thus ?thesis by (auto simp add: succs_def)
    next
      assume "p \<in> ?xs" 
      (* in the following where contains (1+n) not (n+1), the latter will fail to prove *)
      then obtain i where "?isuccs p xs (1+n) i" unfolding succs_def by auto
      hence "?isuccs p (x#xs) n (i +1)" by (simp add: algebra_simps)
      thus ?thesis unfolding succs_def 
        by blast
    qed
  qed
  thus "?x \<union> ?xs \<subseteq> succs (x#xs) n" by blast
qed

lemma succs_simps [simp]: 
  "succs [ADD] n = {n + 1}"
  "succs [LOADI v] n = {n + 1}"
  "succs [LOAD x] n = {n + 1}"
  "succs [STORE x] n = {n + 1}"
  "succs [JMP i] n = {n + 1 + i}"
  "succs [JMPGE i] n = {n + 1 + i, n + 1}"
  "succs [JMPLESS i] n = {n + 1 + i, n + 1}"
  by (auto simp: succs_def isuccs_def)


lemma succs_iexec1:
  assumes "c' = iexec (P!!i) (i,s,stk)" "0 \<le> i" "i < size P"
  shows "fst c' \<in> succs P 0"
  using assms by (auto simp: succs_def isuccs_def split: instr.split)

lemma succs_shift:
  "(p - n \<in> succs P 0) = (p \<in> succs P n)" 
  by (fastforce simp: succs_def isuccs_def split: instr.split)
  
lemma inj_op_plus [simp]:
  "inj ((+) (i::int))"
  by (metis add_minus_cancel inj_on_inverseI)

lemma succs_set_shift [simp]:
  "(+) i ` succs xs 0 = succs xs i"
  by (force simp: succs_shift [where n=i, symmetric] intro: set_eqI)


(* Lemma 8.10 *)
lemma succs_append_otherway [simp]:
  "succs (xs @ ys) n = succs xs n \<union> succs ys (n + size xs)"
proof(induction xs arbitrary:n)
  case Nil
  then show ?case 
    by simp 
    (*using succs_empty*)
next
  case (Cons a xs)
(* 1. \<And>a xs n. (\<And>n. succs (xs @ ys) n = succs xs n \<union> succs ys (n + size xs)) \<Longrightarrow> succs ((a # xs) @ ys) n = succs (a # xs) n \<union> succs ys (n + size (a # xs))*)
  then show ?case by (auto simp: algebra_simps succs_Cons)
qed

text\<open>the following way what written in Compiler2 is doned with exec_n_exec \<close>
(*
lemma succs_append [simp]:
  "succs (xs @ ys) n = succs xs n \<union> succs ys (n + size xs)"
  apply(induct xs arbitrary: n)
   apply(auto simp: succs_Cons algebra_simps)
  done
*)

(* Lemma 8.11 *)
lemma exec_n_exec:
  "P \<turnstile> c \<rightarrow>^n c' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c'"
  apply(induction n arbitrary: c)
   apply simp
  by (meson exec_n.simps(2) star.step)

lemma exec_exec_n:
  "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> \<exists>n. P \<turnstile> c \<rightarrow>^n c'"
  apply(induction rule:star.induct)
  using exec_n.simps(1) apply blast
  using exec_n.simps(2) by blast

lemma exec_eq_exec_n:
  "(P \<turnstile> c \<rightarrow>* c') = (\<exists>n. P \<turnstile> c \<rightarrow>^n c')"
  using exec_exec_n exec_n_exec by blast

(* Lemma 8.12. *)

(* To prove the following lemmas, it is needed to show some of the `succs_xxx`.
Especially, proving exits_simps, this needs simplification of succs lemma named `succs_simps`
 *)
lemma exits_append [simp]:
  "exits (xs @ ys) = exits xs \<union> ((+) (size xs)) ` exits ys - 
                     {0..<size xs + size ys}" 
  by (auto simp: exits_def image_set_diff)
  
lemma exits_single:
  "exits [x] = isuccs x 0 - {0}"
  by (auto simp: exits_def succs_def)
  
lemma exits_Cons:
  "exits (x # xs) = (isuccs x 0 - {0}) \<union> ((+) 1) ` exits xs - 
                     {0..<1 + size xs}" 
  using exits_append [of "[x]" xs]
  by (simp add: exits_single)

lemma exits_empty [iff]: "exits [] = {}" by (simp add: exits_def)

lemma exits_simps [simp]:
  "exits [ADD] = {1}"
  "exits [LOADI v] = {1}"
  "exits [LOAD x] = {1}"
  "exits [STORE x] = {1}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMP i] = {1 + i}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMPGE i] = {1 + i, 1}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMPLESS i] = {1 + i, 1}"
  by (auto simp: exits_def)

lemma acomp_succs [simp]:
  "succs (acomp a) n = {n + 1 .. n + size (acomp a)}"
  apply(induction a arbitrary: n)
    apply(auto simp: exits_def)
  done
(*In the above lemma, `apply(auto simp: exits_def)` needs many subgoals.
So you need prove them as lemma named "exits_simps".
*)

lemma acomp_size:
  "(1::int) \<le> size (acomp a)"
  apply(induction a)
    apply(auto)
  done

lemma acomp_exits [simp]:
  "exits (acomp a) = {size (acomp a)}"
  apply(auto simp: acomp_size exits_def)
  done


(* Lemma 8.13. 
we settle for providing an upper bound on the possible successors of bcomp.
*)

lemma bcomp_succs:
  "0 \<le> i \<Longrightarrow>
  succs (bcomp b f i) n \<subseteq> {n .. n + size (bcomp b f i)}
                           \<union> {n + i + size (bcomp b f i)}" 
proof(induction b arbitrary: f i n)
  case (Bc x)
  then show ?case by auto
next
  case (Not b)
  then show ?case by auto
next
  case (And b1 b2)
  from And.prems
  show ?case by (cases f) (auto dest: And.IH [THEN subsetD, rotated]) 
next
  case (Less x1a x2a)
  then show ?case by auto
qed

lemmas bcomp_succsD [dest!] = bcomp_succs [THEN subsetD, rotated]
(* theorem bcomp_succsD: 
?c \<in> succs (bcomp ?b ?f ?i) ?n \<Longrightarrow> 
0 \<le> ?i \<Longrightarrow> 
?c \<in> {?n..?n + size (bcomp ?b ?f ?i)} \<union> {?n + ?i + size (bcomp ?b ?f ?i)} *)

lemma bcomp_exits:
  fixes i :: int
  shows 
  "0 \<le> i \<Longrightarrow>
  exits (bcomp b f i) \<subseteq> {size (bcomp b f i), i + size (bcomp b f i)}"
  apply(auto simp:exits_def)
  done

lemma bcomp_exitsD [dest!]:
  "p \<in> exits (bcomp b f i) \<Longrightarrow> 0 \<le> i \<Longrightarrow> 
  p = size (bcomp b f i) \<or> p = i + size (bcomp b f i)"
  using bcomp_exits by auto

(* Lemma 8.14. *)

lemma ccomp_succs:
  "succs (ccomp c) n \<subseteq> {n..n + size (ccomp c)}"
proof(induction c arbitrary: n)
  case SKIP
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  from Seq.prems
  show ?case by (fastforce dest: Seq.IH[THEN subsetD])
next
  case (If x1 c1 c2)
  from If.prems
  show ?case by (auto dest: If.IH[THEN subsetD] simp: isuccs_def succs_Cons)
next
  case (While x1 c)
  from While.prems
  show ?case by (auto dest: While.IH[THEN subsetD])
qed

lemma ccomp_exits:
  "exits (ccomp c) \<subseteq> {size (ccomp c)}"
  using ccomp_succs [of c 0] by (auto simp: exits_def)

(* Lemma 8.15 (Decomposition of machine executions). *)
lemma exec_Suc:
  "\<lbrakk> P \<turnstile> c \<rightarrow> c'; P \<turnstile> c' \<rightarrow>^n c'' \<rbrakk> \<Longrightarrow> P \<turnstile> c \<rightarrow>^(Suc n) c''" 
  by (fastforce simp del: split_paired_Ex)

lemma exec_n_Nil [simp]:
  "[] \<turnstile> c \<rightarrow>^k c' = (c' = c \<and> k = 0)"
  by (induct k) (auto simp: exec1_def)

lemma exec1_exec_n [intro!]:
  "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c \<rightarrow>^1 c'"
  by (cases c') simp

lemma exec1_split:
  fixes i j :: int
  shows
  "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow> (j,s') \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size c \<Longrightarrow> 
  c \<turnstile> (i,s) \<rightarrow> (j - size P, s')"
  apply(auto simp: exec1_def)
  apply(auto split: instr.splits)
  done

lemma exec_n_split:
  fixes i j :: int
  assumes "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow>^n (j, s')"
          "0 \<le> i" "i < size c" 
          "j \<notin> {size P ..< size P + size c}"
  shows "\<exists>s'' (i'::int) k m. 
                   c \<turnstile> (i, s) \<rightarrow>^k (i', s'') \<and>
                   i' \<in> exits c \<and> 
                   P @ c @ P' \<turnstile> (size P + i', s'') \<rightarrow>^m (j, s') \<and>
                   n = k + m" 
using assms proof (induction n arbitrary: i j s)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  have i: "0 \<le> i" "i < size c" by fact+
  from Suc.prems
  have j: "\<not> (size P \<le> j \<and> j < size P + size c)" by simp
  obtain i0 s0 where
    step: "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow> (i0,s0)" and
    rest: "P @ c @ P' \<turnstile> (i0,s0) \<rightarrow>^n (j, s')"
    using Suc.prems(1) by auto
  from step i
  have c: "c \<turnstile> (i,s) \<rightarrow> (i0 - size P, s0)" by(rule exec1_split) 

  have "i0 = size P + (i0 - size P) " by simp
  then obtain j0::int where j0: "i0 = size P + j0" ..

note split_paired_Ex [simp del]

  have ?case if assm: "j0 \<in> {0 ..< size c}"
  proof -
    from assm j0 j rest c
    show ?case by (fastforce dest!: Suc.IH intro!: exec_Suc)
  qed
  moreover have ?case if assm: "j0 \<notin> {0 ..< size c}"
  proof -
    from c j0 have "j0 \<in> succs c 0" 
      by (auto dest: succs_iexec1 simp: exec1_def simp del: iexec.simps)
    with assm have "j0 \<in> exits c" by (simp add: exits_def)
    with c j0 rest show ?case by fastforce
    (* exec1_exec_n is needed to prove over case. *)
(*      by (metis add.commute add.left_neutral add_Suc diff_eq_eq exec_n.simps(1) exec_n.simps(2)) *)
  qed
  ultimately show ?case 
    by blast
qed

theorem ccomp_exec: "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size (ccomp c), t, stk) \<Longrightarrow> (c,s) \<Rightarrow> t"
  sorry

end