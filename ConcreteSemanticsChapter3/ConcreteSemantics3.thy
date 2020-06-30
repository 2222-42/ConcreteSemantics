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

subsubsection "3_1_Exercise"

(* Exercise 3.1 *)

(* checks that its argument does not contain a subexpression of the form Plus (N i) (N j ). *)
fun optimal :: "aexp => bool" where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus a b) = ((optimal a) \<and> (optimal b))"

lemma "optimal (asimp_const a)"
apply(induction a)
apply(auto split: aexp.split)
done

(* Exercise 3.2 *)

(* datatype classedAexp = Natural aexp | OnlyVariables aexp | Operation aexp aexp *)
(* From the following definitions, I produce the unexpected cases in the below convertClassedAexpToAexp.
To exclude OnlyVariables and Operation from `Natural {hoge}`.
 *)

 datatype classedAexp = Natural int | OnlyVariables aexp | Operation aexp int

(* to set (N n) at the latest of the formula *)
fun convertClassedAexpToAexp :: "classedAexp => aexp" where
"convertClassedAexpToAexp (Natural n) = N n" |
"convertClassedAexpToAexp (OnlyVariables x) = x" |
"convertClassedAexpToAexp (Operation e1 n) = Plus e1 (N n)"

fun fullPlusNatural :: "int => classedAexp => classedAexp" where
"fullPlusNatural n cexp = 
 (if n = 0
  then cexp
  else case cexp of
    Natural m => Natural (n + m) |
    OnlyVariables e => Operation e n |
    Operation e1 m => Operation e1 (n + m)
  )"
    (* 
    In order to prove lemma aval_fullPlusNatural
    To exclude some of V cases from `OnlyVariables {hoge}`
    OnlyVariables (V x) => Operation (V x) n | *)

fun full_asimp2 :: "aexp => classedAexp" where
"full_asimp2 (N n) = Natural n" |
"full_asimp2 (V x) = OnlyVariables (V x)" |
"full_asimp2 (Plus a b) = 
    (case (full_asimp2 a, full_asimp2 b) of
        (Natural n, e) => fullPlusNatural n e |
        (e, Natural m) => fullPlusNatural m e |
        (OnlyVariables x, OnlyVariables y) => OnlyVariables (Plus x y) |
        (OnlyVariables x, (Operation e2 n)) => Operation (Plus x e2) n |
        ((Operation e1 n), OnlyVariables y) => Operation (Plus e1 y) n |
        ((Operation e1 n), (Operation e2 m)) => Operation (Plus e1 e2) (n + m) 
    )"

fun full_asimp1 :: "aexp => aexp" where
"full_asimp1 exp = convertClassedAexpToAexp (full_asimp2 exp)"

lemma aval_fullPlusNatural: "aval (convertClassedAexpToAexp(fullPlusNatural n e)) s = n + (aval (convertClassedAexpToAexp e) s)"
apply(induction e)
apply(auto split: classedAexp.split)
done

lemma "aval (full_asimp1 e) s = aval e s"
(* apply(induction rule: full_asimp1.induct) *)
apply(induction e)
apply(auto split: classedAexp.split)
done

(* From the following stash, I implement the above the classified datatype*)
(* The following texts are stash. It produces only insane subgols *)
(* to set (N n) at the latest of the formula *)
(* fun fullPlusNatural :: "int => aexp => aexp" where
"fullPlusNatural n e = 
 (if n = 0
  then e
  else case e of
    N m => N (n + m) |
    V x => Plus (V x) (N n) |
    Plus (V x) (V y) => Plus (Plus (V x) (V y)) (N n) |
    Plus e1 (N m) => Plus e1 (N (n + m)) |
    Plus e1 e2 => Plus (Plus e1 e2) (N n)
  )"

value "fullPlusNatural 3 (Plus (N 2) (V x))"


fun full_asimp2 :: "aexp => aexp" where
"full_asimp2 (N n) = N n" |
"full_asimp2 (V x) = V x" |
"full_asimp2 (Plus a b) = 
    (case (full_asimp2 a, full_asimp2 b) of
        (N n, e) => fullPlusNatural n e |
        (e, N m) => fullPlusNatural m e |
        (V x, V y) => Plus (V x) (V y)|
        (V x, (Plus e2 (N n))) => Plus (Plus (V x) e2) (N n)|
        ((Plus e1 (N n)), V y) => Plus (Plus e1 (V y)) (N n) |
        ((Plus e1 (N n)), (Plus e2 (N m))) => Plus (Plus e1 e2) (N(n + m)) |
        (e1, Plus e2 (V y)) => Plus (V y) (Plus e1 e2)|
        (e1, Plus (V x) e2) => Plus (V x) (Plus e1 e2) |
        (Plus e2 (V y), e1) => Plus (V y) (Plus e1 e2)|
        (Plus (V x) e2, e1) => Plus (V x) (Plus e1 e2) 
    )" *)
(* Critical Problem is the following only contains variables:
e.g., Plus (V x) (Plus (V z) (V y)) *)
(* value "full_asimp2 (Plus (V x) (Plus (V z) (V y)))"
value "full_asimp2 (Plus (Plus (V z) (V y)) (V x) ) "

value "full_asimp2 (Plus(N 1) (Plus (V x ) (N 2)))"
value "full_asimp2 (Plus (N 1) (N 2))"
value "full_asimp2 (Plus (N 1) (Plus (V x) (N 2)))"
value "full_asimp2 (Plus (N 2) (Plus (V y) (V x)))"
(* "fullPlusNatural 2 (Plus (V y) (V x))" *)
(*  *)


value "full_asimp2 (Plus (V y) (Plus (V x) (N 2)))"
value "full_asimp2 (Plus (Plus(N 3)(V y)) (Plus (V x) (N 2)))"
value "full_asimp2 (Plus (N 3) (Plus (Plus (V x) (Plus (V y) (N 2) )) (V z)))"
value "full_asimp2 (Plus (N 1) (Plus (Plus (N 2) (V x)) (V y)))"

value "full_asimp2 (Plus (N 1) (Plus (Plus (V y) (V x)) (N 2)))"
(* value "full_asimp2 (Plus (N 1) (Plus (Plus (Plus (V x) (V y)) (N 3)) (N 2)))" *)
(* "fullPlusNatural 1 (fullPlusNatural 2 (Plus (V y) (V x)))" *)
value "full_asimp2 (Plus (Plus (Plus (V y) (V x)) (N 2)) (N 1))"
(* "full_asimp2 (Plus (Plus (Plus (V y) (V x)) (N 2)) (N 1))" *)
 *)

(* lemma aval_fullPlusNatural: "aval (fullPlusNatural n e) s = n + (aval e s)"
apply(induction rule: fullPlusNatural.induct)
sledgehammer *)

 (* 2. 

       aval x31 s + s x2 = aval a s \<Longrightarrow>
       s x2a = aval b s \<Longrightarrow>
       full_asimp2 b = V x2a \<Longrightarrow>
       full_asimp2 a = Plus x31 (V x2) \<Longrightarrow> aval undefined s = aval a s + aval b s

 *)

end