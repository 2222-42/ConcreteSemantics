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

subsubsection "3.1.3 Constant Folding"

(* 
constant folding:
- One of Program Optimization
- the replacement of constant subexpressions by their value.
*)

fun asimp_const :: "aexp => aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) = 
    (case (asimp_const a1, asimp_const a2) of 
        (N n1, N n2) => N (n1 + n2) |
        (b1, b2) => Plus b1 b2)"

(* In the above declaration of function "asimp_const", 
'b1' and 'b2' are simplified as 'asimp_const a1' and 'asimp_const a2' *)

(* `asimp_const` is correct, does not change the semantics, does not change the value of its argument *)
lemma "aval (asimp_const a) s = aval a s"
apply(induction a)
apply(auto split: aexp.split)
(* The split modifier is the hint to auto to perform a case split whenever it sees a case expression over aexp. *)
done

(* Plus (N 0) a and Plus a (N 0) should be replaced by a. *)
(* 
Instead of extending asimp_const 
we split the optimization process into two functions: 
- one performs the local optimizations, 
- the other traverses the term.
*)

fun plus :: "aexp => aexp => aexp" where
"plus (N i1) (N i2) = N(i1 + i2)" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"


lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
(* The proof is by induction on a1 and a2 using the computation induction rule for plus (plus:induct) *)
apply(induction rule: plus.induct)
apply(auto split: aexp.split)
done

(* Now we replace Plus by plus in a bottom-up manner throughout an expression *)
fun asimp:: "aexp => aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

(* 
The new lemma is different from the previous lemma:
    lemma "aval (asimp_const a) s = aval a s"
, because this performs in bottom-up manner.
*)
lemma "aval (asimp a) s = aval a s"
apply(induction a)
apply(auto split: aexp.split)
(* sledgehammer *)
by (simp add: aval_plus)

end