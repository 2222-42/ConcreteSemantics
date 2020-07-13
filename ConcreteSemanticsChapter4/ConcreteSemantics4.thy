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

end