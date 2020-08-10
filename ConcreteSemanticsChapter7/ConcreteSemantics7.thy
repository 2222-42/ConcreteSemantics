theory ConcreteSemantics7
  imports Main 
begin

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

 (* value "''x''  ::= Plus(V ''y'')(N 1);; ''y''  ::= N 2"
 value "x := y + 1; y := 2" *)

text \<open> 
even the more concrete Isabelle notation above is occasionally somewhat cumbersome to use.
one could write separate parsing/printing ML code that integrates with Isabelle and implements the concrete syntax of the language.
\<close>

text \<open>
Therefore definitions and theorems about
the core language only need to worry about one type of loop, while still supporting
the full richness of a larger language. This significantly reduces proof
size and effort for the theorems that we discuss in this book.
\<close>
end