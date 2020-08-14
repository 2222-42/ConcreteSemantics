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

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
sorry

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
  case (WhileFalse b s c)
  then show ?case sorry
next
  case (WhileTrue b s1 c s2 s3)
  then show ?case sorry
qed

end