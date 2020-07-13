theory ConcreteSemantics4
  imports Main
begin

section "4 Logic and Proof Beyond Equality"

subsection "4.1 Formulas"
(* = has a higher precedence than the other logical operators. *)
(* where  <-> has the same low precedence as --> *)

(* 論理的には同じでも、==>の方がIsabelleのFrameworkの中の話だから、証明が楽になるよ *)
(* The implication ==> is part of the Isabelle framework. 
It structures theorems and proof states, separating assumptions from conclusions *)
(* The implication --> is part of the logic HOL and can occur inside the formulas that make up the assumptions and conclusion. *)

subsection "4.2 Sets"

(* 
UNIV is the set of all elements of some type.
Set comprehension is written {x. P} rather than {x | P}.
*)

(* 
\<union> union
\<inter> inter

\<Union> and Union,
\<Inter> and Inter.

UN x:A. B and INT x:A. B where x may occur in B.
If A is UNIV you can write UN x. B and INT x. B.
*)

(* 
set :: 'a list => 'a set 
    converts a list to the set of its elements

finite :: 'a set => bool
     is true iff its argument is finite

card :: 'a set => nat
    is the cardinality of a finite set and is 0 for all infinite sets

f ‘ A = {y:  \E x \in A. y = f x }
     is the image of a function over a set
*)

subsubsection "Exercises"

(* Exercise 4.1. *)

datatype 'a tree = Tip | Node "'a tree" 'a " 'a tree"

(* Define a function 
    set :: 'a tree => 'a set 
that returns the elements in a tree *)
fun set :: "'a tree => 'a set" where
"set Tip = {}" |
"set (Node L a R) = {a} \<union> (set L) \<union> (set R)"

(* and a function
    ord :: int tree => bool 
that tests if an int tree is ordered *)

(* 
左の枝が小さいと仮定する
左の枝の最大値は親のより小さく
右の枝の最小値はと親のより大きい
*)

(* fun ord :: "int tree => bool" where
"ord Tip = True" |
"ord (Node L a R) = True" *)

(* Define a function ins 
- that inserts an element into an ordered int tree
- while maintaining the order of the tree
- If the element is already in the tree, the same tree should be returned.
*)

(* Prove correctness of ins: 
set (ins x t) = {x} \union set t and ord t => ord (ins i t)
. *)

end