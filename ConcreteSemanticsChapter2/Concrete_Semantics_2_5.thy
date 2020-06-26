theory Concrete_Semantics_2_5
  imports Main
begin

(* 2.5 *)

(* Simplification means that
- using equations l = r from left to right (only),
- as long as possible.
*)

(* equations that have been given the `simp` attribute are called simplification rules. *)

(* The proof tool that performs simplifications is called the simplifier. *)

(*
 Simplification is often also called `rewriting` and
 simplification rules `rewrite rules`
*)


(* 2.5.1 *)

(*
Simplification samples:
- datatype the distinctness and injectivity rules, 
- fun the defining equations.
- Nearly any theorem can become a simplification rule
*)

(*
Not Automatically simplification: 
 Definitions are not declared as simplification rules automatically! 
*)

(*
Remarks on simplification rule:
- Only equations that really simplify should be declared as simplification rules 
- Distributivity laws, for example, alter the structure of terms and can produce an exponential blow-up.
*)

(* 2.5.2 *)

(* 
Simplification rules can be conditional. 
Before applying such a rule, the simplifier will first try to prove the preconditions, again by simplification.
*)

(* 2.5.3 *)

(* Simplification can run forever, *)
(* It is the user’s responsibility not to include simplification rules that can lead to nontermination *)

(*
Remarks on Simplification:
- The right-hand side of a simplification rule should always be “simpler” than the left-hand side — in some sense.
  - In conditional simplification, all preconditions need to be simpler than the left-hand
side of the conclusion. It leads nontermination when to meet preconditions needs to meet the conclusions.
*)

end