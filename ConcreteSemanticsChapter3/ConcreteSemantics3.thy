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

end