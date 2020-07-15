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
左の部分木が小さいと仮定する
左の部分木の最大値は親のより小さく
右の部分木の最小値はと親のより大きい
さらに、
左の部分木は整列しており
右の部分木は整列している
*)


(*
intのような無限なタイプはenumerableではないから、集合を使った実装ではエラーが起きる。
Infinite types, such as int and nat, are not enumerable, and we cannot 
check for function equality (for the chosen translation above).

The solution to enable execution of this proposition even with an 
infinite type is to choose a different representation for functions (and 
sets).
Different on-going discussions and effort by the developers will soon 
enable that this is possible, but right now, we are at the unlucky stage 
that none of them are fully automatic and could be applied by quickcheck 
behind the scenes.

NB: I am still not happy with the error message. It is the honest truth, 
why quickcheck cannot execute the proposition, but admittedly users 
might struggle understanding its explanation.
ref: https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2011-September/msg00036.html

fun root_is_smaller :: "int * int tree => bool" where
"root_is_smaller(_, Tip) = True" |
"root_is_smaller(a, T) = 
    (let setOfElements = {a. \<forall> x \<in> set T. a \<le> x } in 
        \<forall> x \<in> setOfElements. a \<le> x)"

fun root_is_greater :: "int * int tree => bool" where
"root_is_greater(_, Tip) = True" |
"root_is_greater(a, T) =     (let setOfElements = {a. \<forall> x \<in> set T. a \<ge> x } in 
        \<forall> x \<in> setOfElements. a \<ge> x)"
*)

(*
以下の2つの条件を使えば、 
- 右の枝が常に大きい
- 左の枝が常に大きい

比較する最大の値は取れるのでは

以下のようなケースで整列していないことを示す必要がある
value "ord (Node (Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip)) 3 (Node (Node Tip 2 Tip) 5 Tip))"

条件をよく考えればいかでOKだった
    a \<ge> (getRightestLeafFromTree a L) \<and> 
    a \<le> (getLeftestLeafFromTree a R))"
*)

fun getRightestLeafFromTree :: "int => int tree => int" where
"getRightestLeafFromTree i Tip = i" |
"getRightestLeafFromTree _ (Node L a R) = getRightestLeafFromTree a R"

fun getLeftestLeafFromTree :: "int => int tree => int" where
"getLeftestLeafFromTree i Tip = i" |
"getLeftestLeafFromTree _ (Node L a R) = getLeftestLeafFromTree a L"

fun ord :: "int tree => bool" where
"ord Tip = True" |
"ord (Node L a R) = 
    (ord L \<and> 
    ord R \<and> 
    a \<ge> (getRightestLeafFromTree a L) \<and> 
    a \<le> (getLeftestLeafFromTree a R))"

(* value "ord (Node (Node Tip 2 Tip) 1 (Node Tip 3 Tip))"
value "ord (Node (Node (Node Tip 0 Tip) 2 (Node Tip 1 Tip)) 3 (Node Tip 5 Tip))"
value "ord (Node (Node (Node Tip 3 Tip) 1 (Node Tip 2 Tip)) 3 (Node Tip 5 Tip))"
value "ord (Node (Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip)) 3 (Node (Node Tip 2 Tip) 5 Tip))"
value "ord (Node (Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip)) 3 (Node (Node Tip 4 Tip) 5 Tip))" *)

(* Define a function ins 
- that inserts an element into an ordered int tree
- while maintaining the order of the tree
- If the element is already in the tree, the same tree should be returned.
*)


(* 
以下のように書くと遅いが
"ins x (Node left y right) = (if x = y then (Node left y right)
        else if x < y then Node (ins x left) y right
        else Node left x (ins y right))"

こう書くと早い
"ins a (Node xt b yt) = (if (a = b) then (Node xt b yt) else
                        (if (a < b) then (Node (ins a xt) b yt) else
                        (Node xt b (ins a yt)) ))"

なんで？
-> 普通に実装を間違えていた "Node left x (ins y right))"d / "Node left y (ins x right))"
*)
fun ins :: "int => int tree => int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node left y right) = (if x = y then (Node left y right)
        else if x < y then Node (ins x left) y right
        else Node left y (ins x right))"

(* value "ins 2 (Node (Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip)) 3 (Node (Node Tip 4 Tip) 5 Tip))"
value "(Node (Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip)) 3 (Node (Node Tip 4 Tip) 5 Tip)) 
= (ins 2 (Node (Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip)) 3 (Node (Node Tip 4 Tip) 5 Tip)))"
value "ins 2 (Node (Node (Node Tip 0 Tip) 1 (Node Tip 3 Tip)) 4 (Node (Node Tip 5 Tip) 7 Tip))"
value "ins 6 (Node (Node (Node Tip 0 Tip) 1 (Node Tip 3 Tip)) 4 (Node (Node Tip 5 Tip) 7 Tip))" *)

(* Prove correctness of ins: 
set (ins x t) = {x} \union set t and ord t => ord (ins i t)
. *)

(* 
証明に時間がかかっているので単純化しないといけない
-> insの実装を間違えていたことが原因
*)
lemma "set (ins x t) = {x} \<union> set t" 
apply(induction t)
(* sledgehammer *)
apply(auto)
done

(* 
apply(induction t)
apply(auto)
by (metis getRightestLeafFromTree.simps(1) getRightestLeafFromTree.simps(2) less_trans linorder_neqE_linordered_idom ord.cases)
*)
lemma insPreservesRightIsGreater : "(getRightestLeafFromTree i1 t) < y
                                    ==> i1 < y
                                    ==> i2 < y
                                    ==> (getRightestLeafFromTree i1 (ins i2 t)) < y"
apply(induction t arbitrary: i1)
apply(auto)
done
(* by (metis getRightestLeafFromTree.simps(1) getRightestLeafFromTree.simps(2) less_trans linorder_neqE_linordered_idom ord.cases) *)

lemma insPreservesLefIsSmaller : "(getLeftestLeafFromTree i1 t) > y
                                    ==> i1 > y
                                    ==> i2 > y
                                    ==> (getLeftestLeafFromTree i1 (ins i2 t)) > y"
apply(induction t arbitrary: i1)
apply(auto)
done

(* (2 subgoals):
 1. \<And>t1 x2 t2.
       ord (ins i t1) \<Longrightarrow>
       ord (ins i t2) \<Longrightarrow>
       ord t1 \<Longrightarrow>
       ord t2 \<Longrightarrow>
       getRightestLeafFromTree x2 t1 \<le> x2 \<Longrightarrow>
       x2 \<le> getLeftestLeafFromTree x2 t2 \<Longrightarrow>
       i < x2 \<Longrightarrow> getRightestLeafFromTree x2 (ins i t1) \<le> x2
 2. \<And>t1 x2 t2.
       ord (ins i t1) \<Longrightarrow>
       ord (ins i t2) \<Longrightarrow>
       ord t1 \<Longrightarrow>
       ord t2 \<Longrightarrow>
       getRightestLeafFromTree x2 t1 \<le> x2 \<Longrightarrow>
       x2 \<le> getLeftestLeafFromTree x2 t2 \<Longrightarrow>
       \<not> i < x2 \<Longrightarrow> i \<noteq> x2 \<Longrightarrow> x2 \<le> getLeftestLeafFromTree x2 (ins i t2) *)
lemma "ord t ==> ord (ins i t)"
apply(induction t)
apply(auto)
(* sledgehammer *)
apply (smt insPreservesRightIsGreater )
(* sledgehammer *)
by (smt insPreservesLefIsSmaller)


subsection "4.3 Proof Automation"

(* 
The key characteristics of both `simp` and `auto` are
- They show you where they got stuck, giving you an idea how to continue.
  - simpは証明がどこでスタックするかを見せ、どう続けるかのideaを与えてくれる
- They perform the obvious steps but are highly incomplete.
  - autoは明らかなステップながらもかなり未達成なものをおこなう
*)
(*
Proof Methodがcompleteであるのは、全ての真なるformulasを証明できる場合である。
HOLおよびtheoryにはcompleteなproof methodはない。
IsabelleのProof Methodsはいかに未達成かで異なる。
*)

(* 
fastforceについて
- 最初のsubgoalについてのみ実施する。
- slow versionのforceでは成功するが、fastforceでは失敗することがある
*)

lemma "\<lbrakk> \<forall> xs \<in> A. \<exists> ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n" 
by fastforce

(* 
blastについて
- 複雑な論理的なゴールに対する選択
- is (in principle) a complete proof procedure for first-order formulas, a fragment of HOL. In practice there is a search bound.
  - HOLの断片である、一階の論理式に対しては、completeなproof procedureであり
  - 実践上は探索範囲の束縛がある。
- does no rewriting and knows very little about equality.
  - 書き換えることはなく、等式については少し知っている
- covers logic, sets and relations.
  - 論理、集合、関係についてはカヴァーしている
- either succeeds or fails.
  - 失敗するか成功するかのいずれかである

論理と集合に関する強さと、等式に関する証明の弱さにより、
前のproof methodsを補完する。
*)

lemma "\<lbrakk> \<forall> x y. T x y \<or> T y x; \<forall> x y. A x y \<and> A y x \<longrightarrow> x = y;
        \<forall> x y. T x y \<longrightarrow> A x y \<rbrakk> \<Longrightarrow> \<forall> x y. A x y \<longrightarrow> T x y " 
by blast

subsubsection "4.3.1 Sledgehammer"

(* text と異なり、metisがsuggestされなかった。*)
lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
(* sledgehammer *)
(* using append_eq_append_conv by blast *)
by (metis append_eq_conv_conj )

(* 
Isabelleは外部のツールを信用しておらず、チェック可能な証明を要求する。
  append_eq_conv_conjを合わせて、metisがやっていることがこれ

simpやすでで補題を知っている友人を使うのとは異なり、
metisを手動で使うことは長ったらしくて退屈
  代わりにsledgehammerがやってくれる
*)

(* 
sledgehammerは存在している証明を発見してくれる、という保証はない
また、sledgehammerが他のproof methodsより優れているわけでもない、比較可能なものではない

だから、sledgehammerを使う前に、simpやautoを使うことを勧める
*)

subsubsection "4.3.2 Arithmetic"

(* 
arithmetic formulas: 変数、数、各種演算子(+, -, =, <, <=)、あと一般的な論理結合子を含む式のこと
- これは、線形算術(linear arithmetic)と呼ばれる。
  - 数とのかけ算 `2*n` は許されている

このような式は `arith` で証明される

また、natural numbersのみではなく、integersやreal numbersにも対応している

他にも
- min
- max
*)

lemma "\<lbrakk> (a::nat) \<le> x + b; 2*x < c \<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
(* apply(auto)
done *)
by arith

(* 
autoやsimpも多くの線形算術を証明することはできるが、それはarithの早い(その点で弱い)バージョンによる
だから、必ずしも明示的に呼ぶ必要はない。
*)

end