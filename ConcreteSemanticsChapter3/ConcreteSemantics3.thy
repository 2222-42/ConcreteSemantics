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
value "aval (Plus (N 3) (V ''x''))((\<lambda>x.  0) (''x'' := 7)) "

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

(* Fundamental View: 
- collect (N n) to separate from (V x) 
- Set it is not needed to change the fomula in the Plus A B when A and B are consists of Variables
*)
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


fun subst :: "vname => aexp => aexp => aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if (x = y) then a else (V y))" |
"subst x a (Plus e1 e2) = Plus (subst x a e1) (subst x a e2)"

value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')"

lemma substitution_lemma: "aval (subst x a e) s = aval e (s (x := aval a s))"
apply(induction e)
apply(auto)
done

lemma aval_uniq: "aval a1 s = aval a2 s ==> aval (subst x a1 e) s = aval (subst x a2 e) s "
apply(induction e)
apply(auto)
done

(* Exercise 3.5. *)
datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | PIncr vname | Division aexp2 aexp2

fun get_first :: "val \<times> state \<Rightarrow> val" where
"get_first (a, s) = a"

fun get_first_withOption :: "(val \<times> state)option \<Rightarrow> val option" where
"get_first_withOption None = None" |
"get_first_withOption (Some x) = Some(get_first(x))"

fun get_last :: "val \<times> state \<Rightarrow> state" where
"get_last (a, s) = s"

(* operationPlusWithNoneとoperationDivWithNoneとは共通化できそう
-> operationWithOptionを作った *)
fun operationPlusWithNone :: "(val \<times> state) option => (val \<times> state) option => (val \<times> state) option" where
"operationPlusWithNone a None = None" |
"operationPlusWithNone None b = None" |
"operationPlusWithNone (Some x) (Some y) = Some (get_first(x) + get_first(y), get_last(y))"

fun operationDivWithNone :: "(val \<times> state) option => (val \<times> state) option => (val \<times> state) option" where
"operationDivWithNone a None = None" |
"operationDivWithNone None b = None" |
"operationDivWithNone (Some x) (Some y) = Some (get_first(x) div get_first(y), get_last(y))"
(* 
fun aval2 :: "aexp2 => state => (val \<times> state) option" where
"aval2 (N n) s = (n, s)" |
"aval2 (V x) s = (s x, s)" |
"aval2 (PIncr x) s = (s x, s(x := (s x + 1)))" |
"aval2 (Plus a b) s = ((get_first(aval2 a s) + get_first(aval2 b s)), get_last(aval2 b s)) "


    (* (if (aval2 a s) = None then (if (aval2 b s) = None then None else get_first())) *)
*)
fun aval2 :: "aexp2 => state => (val \<times> state) option" where
"aval2 (N2 n) s = Some(n, s)" |
"aval2 (V2 x) s = Some(s x, s)" |
"aval2 (PIncr x) s = Some(s x, s(x := (s x + 1)))" |
"aval2 (Plus2 a b) s = operationPlusWithNone (aval2 a s) (aval2 b s)" |
"aval2 (Division a b) s = (if (get_first_withOption(aval2 b s) = Some(0)) then None else (operationDivWithNone (aval2 a s) (aval2 b s)))"
(* 
Type unification failed: Clash of types "_ option" and "_ \<times> _"

Type error in application: incompatible operand type

Operator:  get_first :: int \<times> (char list \<Rightarrow> int) \<Rightarrow> int
Operand:   aval2 a s :: (int \<times> (char list \<Rightarrow> int)) option
*)

value "aval2 (N2 2) (\<lambda> x. 1)"
value "aval2
  (Plus2
    (N2 2) (N2 1))
   (\<lambda> x. 1)"

value "aval2
  (Plus2
    (PIncr ''x'')
    (Plus2
      (PIncr ''x'')
      (Division
        (PIncr ''x'')
        (N2 2))))
  (\<lambda> x. 2)"

value "aval2
  (Plus2
    (PIncr ''x'')
    (Plus2
      (PIncr ''x'')
      (Division
        (PIncr ''x'')
        (N2 0))))
  (\<lambda> x. 2)"


fun operationWithOption ::  "(int => int => int) => (val \<times> state) option => (val \<times> state) option => (val \<times> state) option" where
"operationWithOption f a None = None" |
"operationWithOption f None b = None" |
"operationWithOption f (Some x) (Some y)  = Some (f (get_first x) (get_first y), get_last(y))"


fun aval2WithOption :: "aexp2 => state => (val \<times> state) option" where
"aval2WithOption (N2 n) s = Some(n, s)" |
"aval2WithOption (V2 x) s = Some(s x, s)" |
"aval2WithOption (PIncr x) s = Some(s x, s(x := (s x + 1)))" |
"aval2WithOption (Plus2 a b) s = operationWithOption (+) (aval2 a s) (aval2 b s)" |
"aval2WithOption (Division a b) s = (if (get_first_withOption(aval2 b s) = Some(0)) then None else (operationWithOption (div) (aval2 a s) (aval2 b s)))"

value "aval2WithOption
  (Plus2
    (PIncr ''x'')
    (Plus2
      (PIncr ''x'')
      (Division
        (PIncr ''x'')
        (N2 2))))
  (\<lambda> x. 2)"

value "aval2WithOption
  (Plus2
    (PIncr ''x'')
    (Plus2
      (PIncr ''x'')
      (Division
        (PIncr ''x'')
        (N2 0))))
  (\<lambda> x. 2)"


(* Exercise 3.6. *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp => state => int" where
"lval (Nl n) s = n" |
"lval (Vl x) s = s x" |
"lval (Plusl la lb) s = (lval la s) + (lval lb s)" |
"lval (LET x la lb) s = lval lb (s(x := (lval la s)))"
(* かっこの数の問題だった *)

(* 
これまでのNに対して、適切に名前を変えてやらないといけない
Operator:  (=) (inline (Nl n)) :: aexp \<Rightarrow> bool
Operand:   aexp2.N n :: aexp2

as same as V
Operator:  (=) (inline (Vl x)) :: aexp \<Rightarrow> bool
Operand:   aexp2.V x :: aexp2
*)
fun inline :: "lexp => aexp" where
"inline (Nl n) = (N n)" |
"inline (Vl x) = (V x)" |
"inline (Plusl la lb) = (Plus (inline la) (inline lb))" |
"inline (LET x la lb) = subst x (inline la) (inline lb)"

(* HINT: arbitrary:sを付けると、sledgehammerが通る *)
lemma "aval (inline e) s = lval e s"
apply(induction e arbitrary: s)
apply(auto split:lexp.split)
(* sledgehammer *)
by (simp add: substitution_lemma)

subsection "3.2 Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp => state => bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

subsubsection "3.2.1 Constant Folding"

(* define optimizing versions of the constructors *)

fun not :: "bexp => bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc False" |
"not b = Not b"

(* Outer syntax error\<^here>: name expected,
but keyword and\<^here> was found *)
fun "and" :: "bexp => bexp => bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2 = And b1 b2"

fun less :: "aexp => aexp => bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)" |
"less a1 a2 = Less a1 a2"

(* replace the constructors in a bottom-up manner: *)

fun bsimp :: "bexp => bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)" 

subsubsection "Exercises"

(* Exercise 3.7. *)

fun Eq :: "aexp => aexp => bexp" where
"Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
apply(auto)
done

fun Le :: "aexp => aexp => bexp" where
"Le a1 a2 = Not (Less a2 a1)"

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
apply(auto)
done

(* Exercise 3.8. *)

(* an alternative type of boolean expressions *)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

(* First define an evaluation function *)
fun ifval :: "ifexp => state => bool" where
"ifval (Bc2 v) s = v" |
"ifval (If i1 i2 i3) s = (if (ifval i1 s) then (ifval i2 s) else (ifval i3 s))" |
"ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

(* A \land B \equiv A \supset B /\ \neg A \supset \bottom *)
fun b2ifexp :: "bexp => ifexp" where
"b2ifexp (Bc v) = Bc2 v" |
"b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))" |
"b2ifexp (And b1 b2) = (If (b2ifexp b1) (b2ifexp b2) (Bc2 False) )" |
"b2ifexp (Less a1 a2) = Less2 a1 a2" 

fun if2bexp :: "ifexp => bexp" where
"if2bexp (Bc2 v) = Bc v" |
"if2bexp (If i1 i2 i3) = And (Not (And (if2bexp i1) (Not (if2bexp i2)))) (Not (And (Not (if2bexp i1)) (Not (if2bexp i3))))" |
"if2bexp (Less2 a1 a2) = Less a1 a2"

lemma "bval b s = ifval (b2ifexp b) s"
apply(induction b)
apply(auto)
done

lemma "ifval b s = bval (if2bexp b) s"
apply(induction b)
apply(auto)
done

(* Exercise 3.9. *)

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp => (vname => bool) => bool" where
"pbval (VAR x ) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

(* expression is in NNF (negation normal form)
if NOT is only applied directly to VARs
*)
fun is_nnf :: "pbexp => bool" where
"is_nnf (VAR X) = True" |
"is_nnf (NOT (VAR X)) = True" |
"is_nnf (NOT y) = False" |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

 (* that converts a pbexp into NNF by pushing NOT inwards as much as possible. *)
fun nnf :: "pbexp => pbexp" where
"nnf (VAR x) = VAR x" |
"nnf (NOT (VAR x)) = NOT (VAR x)" |
"nnf (NOT (NOT a)) = nnf a" |
"nnf (NOT (OR a b)) = AND (nnf (NOT a)) (nnf(NOT b))" |
"nnf (NOT (AND a b)) = OR (nnf (NOT a)) (nnf(NOT b))" |
"nnf (AND a b) = AND (nnf a) (nnf b)" |
"nnf (OR a b) = OR (nnf a) (nnf b)"

(* Prove that nnf preserves the value (pbval (nnf b) s = pbval b s) and 
nnfが保存するのだから、nnfに関するinductでいいやろ。

returns an NNF (is_nnf (nnf b)) *)
lemma "pbval (nnf b) s = pbval b s"
apply(induction b rule: nnf.induct)
apply(auto)
done

lemma "is_nnf (nnf b)"
apply(induction b rule: nnf.induct)
apply(auto)
done

(* 
DNF (disjunctive normal form) 
if it is in NNF and 
if no OR occurs below an AND.
*)

(* Define a corresponding test is_dnf :: pbexp => bool. *)
(* 
"is_not_the_form_and_or (AND (OR a b) c) = False" | 
"is_not_the_form_and_or (AND a (OR b c)) = False" |
この部分は共通化させたいですね。
*)

fun is_not_the_form_and_or :: "pbexp => bool" where
"is_not_the_form_and_or (VAR x) = True"|  
"is_not_the_form_and_or (NOT y) = True" |
"is_not_the_form_and_or (OR a b) = (is_not_the_form_and_or a \<and> is_not_the_form_and_or b)" |
"is_not_the_form_and_or (AND (OR a b) c) = False" | 
"is_not_the_form_and_or (AND a (OR b c)) = False" |
"is_not_the_form_and_or (AND a b) =  (is_not_the_form_and_or a \<and> is_not_the_form_and_or b)"


fun is_dnf :: "pbexp => bool" where
"is_dnf e = (is_nnf e \<and> is_not_the_form_and_or e)"

(* Define a conversion function dnf_of_nnf :: pbexp ) pbexp from NNF to DNF. *)
(* fun dnf_of_nnf :: "pbexp => pbexp" where
"dnf_of_nnf" *)

end