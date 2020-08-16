theory ConcreteSemantics7_1_2_BigStep
  imports Main "~~/src/HOL/IMP/Com"
begin

section "6 Introduction"

text \<open>
When building upon any of those theories,
for example when solving an exercise, the imports section needs to include
"~~/src/HOL/IMP/T" where T is the name of the required theory
\<close>

section "7 IMP: A Simple Imperative Language"

(* two styles of defining the semantics of a programming language: 
- big-step and 
- small-step operational semantics.
*)

(* As a smaller concrete example, we will apply our semantics to the concept of program equivalence. *)

subsection "7.1 IMP Commands"

text \<open>
Before we jump into any formalization or define the abstract syntax of commands,
we need to determine which constructs the language IMP should contain
\<close>

(* For an imperative language,
we will want the basics such as assignments
*)

 value "''x''  ::= Plus(V ''y'')(N 1);; ''y''  ::= N 2"
 (* value "x := y + 1; y := 2" *)

text \<open> 
even the more concrete Isabelle notation above is occasionally somewhat cumbersome to use.
one could write separate parsing/printing ML code that integrates with Isabelle and implements the concrete syntax of the language.
\<close>

text \<open>
Therefore definitions and theorems about the core language only need to worry about one type of loop, 
while still supporting the full richness of a larger language. 
This significantly reduces proof size and effort for the theorems that we discuss in this book.
\<close>

subsection "7.2 Big-Step Semantics"

text \<open>
use a big-step operational semantics to give meaning to commands.

In an operational semantics setting, 
the aim is to capture the meaning of a program as a relation that describes how a program executes

easier to define and understand,
\<close>

subsubsection "7.2.1 Definition"

text \<open>
In big-step operational semantics, the relation to be defined is between program,initial state, and final state. 
  Intermediate states during the execution of the program are not visible in the relation.
\<close>

(* Predicates in the big-step rules are called "judgements" *)

text \<open>
The idea is 
  to have at least one rule per syntactic construct and 
  to add further rules when case distinctions become necessary.
\<close>


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


subsubsection "7.2.2 Deriving IMP Executions"

text \<open>
state the lemma with a schematic variable and 
let Isabelle compute its value as the proof progresses.
\<close>

schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
apply(rule Seq)
apply(rule Assign)
apply simp
apply(rule Assign)
done
(*
I got theorem
  ex: (''x'' ::= N 5;; ''y'' ::= V ''x'', ?s) \<Rightarrow> ?s
      (''x'' := 5, ''y'' := aval (V ''x'') (?s(''x'' := 5)))

In text, the author wrote that
we get the expected 
(''x'' ::= N 5;; ''y'' ::= V ''x'', s)  \<Rightarrow> s(''x'' := 5, ''y'' := 5)

There seems be merely different.
*)

text\<open>We want to execute the big-step rules:\<close>

code_pred big_step .

text \<open>The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules.\<close>
declare big_step.intros [intro]

text\<open>The standard induction rule 
@{thm [display] big_step.induct [no_vars]}\<close>

thm big_step.induct


values "{t. (SKIP, \<lambda>_.0) \<Rightarrow> t}"

text \<open> Functions cannot always easily be printed, but lists can be, \<close>

values "{map t [''x'', ''y''] | t. (''x'' ::= N 2, \<lambda>_.0) \<Rightarrow> t}"

text \<open>
This section showed us 
  how to construct program derivations and 
  how to execute small IMP programs according to the big-step semantics. 

In the next section, 
we instead 
  deconstruct executions that we know have happened and 
  analyse all possible ways we could have gotten there
\<close>

subsubsection "7.2.3 Rule Inversion"

text \<open>
These inverted rules can be proved automatically by Isabelle from the original rules. 
Moreover, proof methods like auto and blast can be instructed to use 
both the introduction and the inverted rules automatically during proof search.
\<close>

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

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
by blast

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  \<comment> \<open>inverting assms\<close>
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

lemma "(c1;;c2;;c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;;(c2;;c3), s) \<Rightarrow> s'"
proof
  assume "(c1;;c2;;c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where 
    c1: "(c1, s) \<Rightarrow> s1" and 
    "(c2, s1) \<Rightarrow> s2" and
    "(c3, s2) \<Rightarrow> s'"  by blast
    (* This method is not able to be used without the above SeqE. *)
  then have "(c2;;c3, s1) \<Rightarrow> s'" using Seq by auto
  then show " (c1;;(c2;;c3), s) \<Rightarrow> s'" using Seq c1 by auto
next
  assume "(c1;;(c2;;c3), s) \<Rightarrow> s'"
  then show "(c1;;c2;;c3, s) \<Rightarrow> s'"  by (meson Seq SeqE)
qed

text \<open>
Big Stepの証明は基本的に上記の証明と代わりないが、オリジナルの証明の方がわかりやすい。
あと、私の証明では、`by (meson Seq SeqE)`を最後に使っているが、オリジナルではそうではない。
オリジナルのTheoryに入れられているいずれかのlemmaが効いているのであろうが、それはなにか。
\<close>

subsubsection "7.2.4 Equivalence of Commands"

(* semantic equivalence *)
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"

text \<open>
Big_Stepの証明とだいぶ違い、blastで済んでいるが、なぜだ。
\<close>
lemma "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
(* have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t sorry
have "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t sorry *)
 have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t
proof -
  from assm show ?thesis
  proof cases
    case WhileFalse
    thus ?thesis 
      (* using IfFalse Skip  *)
      by blast 
      (* ここで `using IfFalse Skip` が必要にったり明示されたりするのを避けるなら、
      declare big_step.intros [intro]
      が必要 *)
  next
    case WhileTrue
    thus ?thesis by blast
  qed
qed 
moreover have "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t
proof -
  from assm show ?thesis
    proof cases 
      case IfFalse
      thus ?thesis by blast
    next
      case IfTrue
      thus ?thesis by blast
    qed
qed 
ultimately show ?thesis by blast
qed
(* picking this:
    (WHILE b DO c, ?s) \<Rightarrow> ?t \<Longrightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, ?s) \<Rightarrow> ?t
    (IF b THEN c;; WHILE b DO c ELSE SKIP, ?s) \<Rightarrow> ?t \<Longrightarrow> (WHILE b DO c, ?s) \<Rightarrow> ?t 
Illegal application of proof command in "chain" mode 
多分Whileに関するEliminationRuleを入れていないからかな?
=> `proof -`としていなかったことが原因。
*)

lemma "(c) \<sim> (IF b THEN c ELSE c)" (is "?w \<sim> ?iw")
by blast
(* proof -
 have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t 
  proof cases 
    case (bval b s)
    then show ?thesis sorry
  next
    case \<not> (bval b s)
    then show ?thesis sorry
  qed
 moreover have "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t sorry
 ultimately show ?thesis by blast
qed *)

text\<open>
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the \<open>c\<close>, \<open>s\<close>,
and \<open>s'\<close> that we are likely to encounter. Splitting
the tuple parameter fixes this:
\<close>
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
apply (simp add: WhileFalse)
apply (simp add: WhileTrue)
done

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
using sim_while_cong_aux by auto 

text \<open>Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically.\<close>

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto

subsubsection "7.2.5 Execution in IMP is Deterministic"

(* determinism. *)
theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
apply(induction arbitrary: u rule:big_step_induct)
apply(blast+)
done
(* テキストのFig. 7.4. と同じように各ケースを明記してもよいが、全部blastで解決されるため、`blast+`を使う` *)

end