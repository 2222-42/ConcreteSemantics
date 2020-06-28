section "Concrete Semantics Chapter 3"

theory ConcreteSemantics3
  imports Main
begin

subsection "3.1 Arithmetic Expressions"

subsubsection "3.1.1 Syntax"
(* 
Concrete syntax: strings.
    e.g., 2 + (z + 3)

convert the string into a tree for further processing

abstract syntax (tree): the nested structure of the object (two-dimensional trees),
    e.g., Plus (N 2) (Plus (V ''z'') (N 3))
*)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

(* Isabelle strings require two single quotes on both ends, for example ''abc'' *)

(*
They are not same:
- Semantically Equivalece,
- Syncatically Equivalenct,
*)


subsubsection "3.1.2 Semantics"

(* 
The value of all variables is recorded in the (program) state 
The state is a function from variable names to values
*)

type_synonym val = int
type_synonym state = "vname => val"

fun aval :: "aexp => state => val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x.0)"

(* 
the generic function update notation f (a := b) is used: 
    the result is the same as f, except that it maps a to b:
        f (a := b) = (\<lambda>x. if x = a then b else f x )

"((\<lambda>x.0) (''x'' := 7))(''y'' := 3)" maps ''x'' to 7, ''y'' to 3
<''x'' := 7; ''y'' := 3>: which works for any number of variables, even for none: <> is syntactic sugar for \<lambda>x : 0.
*)


end