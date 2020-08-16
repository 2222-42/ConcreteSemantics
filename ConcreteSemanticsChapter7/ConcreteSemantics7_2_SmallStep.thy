theory ConcreteSemantics7_2_SmallStep
  imports Main "~~/src/HOL/IMP/Com" "~~/src/HOL/IMP/Star" "~~/src/HOL/IMP/Big_Step"
begin

section "7 IMP: A Simple Imperative Language"

subsection "7.3 Small-Step Semantics"

(* a different way of defining the semantics of IMP. *)

text \<open>
the purpose of a small-step semantics:
  allow us to explicitly observe intermediate execution states.

The main idea for representing a partial execution is 
to introduce the concept of how far execution has progressed in the program.
  "com * state \<Rightarrow> com * state \<Rightarrow> bool"
  2nd "com * state" component of the judgement is 
  use the command SKIP to indicate that execution has terminated
\<close>

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"
text \<open> for the WHILE loop: we define its semantics by merely unrolling the loop once. 
Note that we could have used the unrolling definition of WHILE in the big-step semantics as well.(cf: section 7.2.4)
\<close>

code_pred small_step .
declare small_step.intros [intro]
thm small_step.induct
lemmas small_step_induct = small_step.induct[split_format(complete)]
thm small_step_induct

abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

values "{(c', map t [''x'', ''y'', ''z'']) | c' t. (''x'' ::= V ''z'';; ''y'' ::= V ''x'',<''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c', t)}"
(* 
"{(''x'' ::= V ''z'';; ''y'' ::= V ''x'', [3, 7, 5]),
  (SKIP;; ''y'' ::= V ''x'', [5, 7, 5]), (''y'' ::= V ''x'', [5, 7, 5]),
  (SKIP, [5, 5, 5])}"
  :: "(com \<times> int list) set"
*)

(* こいつらがないとdeterministicの証明ができない *)
inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"


lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule:small_step.induct)
apply blast+
done

(* lemma deterministic':
  "\<lbrakk> cs \<rightarrow> cs' ; cs \<rightarrow> cs'' \<rbrakk> \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule:small_step.induct)
apply blast+
done *)

subsubsection "7.3.1 Equivalence with Big-Step Semantics"

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof (induction rule: star_induct)
  case (refl x)
  then show ?case by simp
next
  case (step x y z)
  then show ?case by (metis Seq2 star.step)
qed


lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
by (meson Seq1 star.step star_seq2 star_trans)

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof(induction rule: big_step.induct)
  case (Skip s)
  then show ?case by blast
next
  case (Assign x a s)
  then show ?case by blast
next
  case (Seq c1 s1 s2 c2 s3)
  assume "(c1,s1) \<rightarrow>* (SKIP,s2)" and "(c2,s2) \<rightarrow>* (SKIP,s3)"
  (* here is gap *)
  then show ?case using seq_comp by blast
next
  case (IfTrue b s c1 t c2)
  assume "bval b s" and "(c1, s) \<rightarrow>* (SKIP, t)"
  hence "(IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)"  by (simp add: small_step.IfTrue)
  then show ?case by (meson IfTrue.IH star.step)
next
  case (IfFalse b s c2 t c1)
  assume "\<not> bval b s" and "(c2, s) \<rightarrow>* (SKIP, t)"
  hence "(IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" by (simp add: small_step.IfFalse)
  then show ?case by (meson IfFalse.IH star.step)
next
(* WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" *)
  case (WhileFalse b s c)
  assume "\<not>bval b s"
  have "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"  by (simp add: While)
  moreover have "(IF b THEN c;; WHILE b DO c ELSE SKIP,s) \<rightarrow>* (SKIP, s)"  by (simp add: WhileFalse.hyps small_step.IfFalse)
  ultimately show ?case  by (meson star.step)
  (* then ... by (meson calculation star.step) *)
next
(* WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"  *)
  case (WhileTrue b s1 c s2 s3)
  assume b: "bval b s1" and c: "(c,s1) \<Rightarrow> s2" and w: "(WHILE b DO c, s2) \<Rightarrow> s3"
  have "(WHILE b DO c, s1) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, s1)" by blast
  moreover have "(IF b THEN c;; WHILE b DO c ELSE SKIP, s1) \<rightarrow>* (c;;WHILE b DO c, s1)"  by (simp add: b small_step.IfTrue)
  moreover have  "(c;; WHILE b DO c,s1) \<rightarrow>* (SKIP, s3)" using WhileTrue.IH(1) WhileTrue.IH(2) seq_comp by auto
  ultimately show ?case  by (meson star.step star_trans)
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
  apply(induction arbitrary: t rule: small_step.induct)
  apply(auto)
  done
  

lemma small_to_big:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
  apply(induction cs "(SKIP, t)" rule: star.induct)
  apply(auto)
  by (simp add: small1_big_continue)

theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
  using big_to_small small_to_big by blast


subsubsection "7.3.2 Final Configurations, Infinite Reductions, and Termination"

definition final :: "com \<times> state \<Rightarrow> bool" where
"final cs \<longleftrightarrow> \<not>(\<exists> cs'. cs \<rightarrow> cs')"

lemma final_then_skip: "final (c,s) \<Longrightarrow> (c = SKIP)"
(* final_def はinductionの先におかないと *)
apply(simp add: final_def)
apply(induction c)
apply blast+
done

lemma skip_is_final: "(c = SKIP) \<Longrightarrow> final (c,s)"
 using final_def by auto

lemma finality_equivalent_skip: "final (c,s) = (c = SKIP)"
using final_then_skip skip_is_final by blast

text \<open> 
This lemma says that in IMP the absence of a big-step result is equivalent to non-termination.

In the bigstep semantics this is often indistinguishable from non-termination. 
In the small-step semantics the concept of final configurations neatly distinguishes the two causes.
\<close>
lemma "(\<exists> t. cs \<Rightarrow> t ) \<longleftrightarrow> (\<exists> cs'. cs \<rightarrow>* cs' \<and> final cs')"
apply(simp add: finality_equivalent_skip)
using big_to_small small_to_big by blast

end