theory ConcreteSemantics7
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

code_pred big_step .

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

inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE

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


end