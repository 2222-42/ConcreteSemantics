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

end