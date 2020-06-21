theory Concrete_Semantics_2_3
  imports Main
begin

(* 2.3 *)
(* Type synonyms are abbreviations for existing types, *)
(* Type synonyms are expanded after parsing and are not present in internal
representation and output. *)

(* 2.3.1 *)
(* It introduces the constructors C_{i} :: T_{i,1} => ... => T{i,n_{i}} => ( 'a_{1}, ..., 'a_{n})t
and expresses that any value of this type is built from these constructors in
a unique manner. *)
(*
niqueness is implied by the following properties of the
constructors:
- Distinctness
- Injectivity
*)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree => 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
apply(induction t)
apply(auto)
done

datatype 'a option = None | Some 'a

fun lookup :: "('a * 'b) list => 'a => 'b option" where
"lookup [] x = None" |
"lookup ((a, b) # ps) x = (if a = x then Some b else lookup ps x)"

(* 2.3.2 *)
(* Non-recursive functions can be defined. *)
(* Such definitions do not allow pattern matching but only f x_1 ... x_n = t *)

definition sq :: "nat => nat" where
"sq n = n * n"

(* 2.3.3 *)
(* Abbreviations are similar to definitions *)

abbreviation sq' :: "nat => nat" where
"sq' n \<equiv> n * n"
(* The key difference is that sq' is only syntactic sugar: after parsing, sq' t is
replaced by t * t; before printing, every occurrence of u * u is replaced by
sq' u. Internally, sq' does not exist. *)

(* definitions need to be expanded explicitly (Section 2.5.5)
whereas abbreviations are already expanded upon parsing *)

(* abbreviations should be introduced sparingly *)

end