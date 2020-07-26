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
`blast`について
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

subsubsection "4.3.3 Trying Them All"

(* 
上記の自動証明手法の全てを使いたいのだったら
`try`
と打ち込めばいい。

軽量バージョンの
`try0`
はsledgehammerを呼ばない。

`try0 simp: ... intro: ...`
とすれば、特定のsimpification や introduction ruleを追加することもできる。
*)

subsection "4.4 Single Step Proofs"

(* 
ある自動証明の手法で失敗したら、proof ruleの段階的(stepwise)な適用が必要になる

たとえば、A /\ B　の証明で失敗したら、これを二つに、AとBに分けたい。
これは conjunction introduction (conjI)によってなされる。
*)

subsubsection "4.4.1 Instantiating Unknowns"

(* 
定理を証明し終えたら、Isabelleはそこに表れる自由変数xをunknownsと呼ばれる ?xに置き換える
*)

(* 
- conjI [of "a=b" "False"] instantiates the unknowns in conjI from left to right
  - `th[of string1 ... stringn]` instantiates the unknowns in the theorem `th` from left to right 
  with the terms string1 to stringn
  - 全部のunknownsのインスタンスを生成する必要がない場合、 `conjI[of _ "False"]`と、 `_` を使うことでスキップすることができる
- Unification is the process of making two terms syntactically equal by suitable instantiations of unknowns
  - For example, unifying `?P ^ ?Q` with `a = b ^ False` instantiates `?P` with `a = b` and `?Q` with `False`
  - 明示的に名前を付けて初期化することもできる `conjI[where ?P = "a=b" and ?Q = "Flase"]`と。
*)

subsubsection "4.4.2 Rule Application"

(* 
Rule application とは、証明の状態に対して、前に戻るルール(rule backwards)を適用することである 

例:
1. ... ==> A /\ B
という証明状態(proof state)に`conjI`を使うと、2つのサブゴール
sub1. ... ==> A
sub2. ... ==> B
が作られる。

\<lbrakk> A1; ...; An \<rbrakk> \<Longrightarrow> A
という規則をあるサブゴール
... ==> C
に適用することは2つのStepを踏んで進む
1. AとCをUnifyし、ルールの中のunknownsのインスタンスを生成する
2. サブゴールCを新たなサブゴールA1からAnまでと置き換える
*)

(* 
rule xyzを適用するコマンド：
  aply(rule xyz)

これは、rule xyzでの(backchaining)と、呼ばれもする。
*)

subsubsection "4.4.3 Introduction Rules"

(* 
introduction rules: 
  They explain under which premises some logical construct can be introduced
  導入規則は、どの前提において、論理構成子が導入されたのかを説明してくれる

eg.
- conjI
- impI
- allI
- iffI

these rules are helpful in locating where and why automation fails.
  自動証明がどこでどうして失敗したのかを示すのに役立つ
*)

(* 
Isabelleは色々な導入規則をしっているから、以下のコマンドの入力によって、
現在のサブゴールに対して適切な規則を自動で選ぶ：
  apply rule
*)

(* 
`intro`を使えば、自分の定理をintroduction ruleに追加することができる

けれどintro attributeには注意を払わなくてはいけない、
  なぜなら、探索空間を増やし、非決定に導くから。

使うときは, `blast` もしくはそれに近いものを呼び出す中でのみ使うことが推奨される。
*)

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
(* apply(auto) *)
by(blast intro: le_trans)

subsubsection "4.4.4 Forward Proof"

(* Forward proof は古い定理から新しい定理を導出すること
- 他のルールへのルールの適用(Application of rules to other rules) は前向きに動作する;前提から結論へ
- 証明状態へのルールの適用(application of rules to proof states)は後ろ向きに動作する;結論から前提へ
*)

(* 
すでに`conjI`でも見てたが、`of`がそれ。
  これは自由変数に対して適用する。
`OF`は定理に対して適用する

Given 
- a theorem `A ==> B` called r and 
- a theorem `A'` called `r'` 
, 

-> the theorem `r [OF r']` is the result of applying `r` to `r'` ,
  where `r` should be viewed as a function taking a theorem `A` and returning `B`. 
  
More precisely, 
- `A` and `A'` are unified(AとA'が統一されていて(これがなされていないと失敗する)), 
- thus instantiating the unknowns in `B`(Bの中のunknownsのインスタンスを生成して), 
- and the result(`r [OF r']`) is the instantiated `B`(結果が、Bのインスタンスを生成したものになる).
*)

(* 使い方：
r が \<lbrakk> A1, ... , An \<rbrakk> => A という形の時
m \<le> n で、r1からrmまでが定理であるとして、
これらに対して、それらを、unifyして、証明することで
  r [OF r1 ... rm]
が得られる。

例:
  thm conjI [OF refl[of "a"] refl[of "b"]]

なお、
- refl は `?t = ?t` の定理
- thm は結果のみを出すだけのコマンド

これによって、a = a \<and> b = b が得られる。
*)

(* 
Forward reasoningは証明状態(proof states)に関連しても意味をなす

modifier の `dest` を使えば、特定のルールを前進に使うように、proof methodに指令するようにできる

modifier `dest: r` allows proof search to reason forward with r, 
  i.e., to replace an assumption A', where A' unifies with A, 
  with the correspondingly instantiated B
*)

lemma "Suc(Suc(Suc a)) \<le> b ==> a \<le> b"
by(blast dest: Suc_leD)

(* 
この例について

blastは複雑な論理式に対して適用する

Suc_leDでbackchainすることもできるが、
前提が結論より複雑だから、backchainすることは非決定を導く
*)

subsection "4.5 Inductive Definitions"

(* they are the key construct in the definition of operational semantics in the second part of the book *)

subsubsection "4.5.1 An Example: Even Numbers"

(* The operative word “inductive” means that these are the only even numbers *)
(* In Isabelle we give the two rules the names `ev0` and `evSS` *)

inductive ev :: "nat => bool" where
ev0: "ev 0"|
(* evSS: "ev n ==> ev(n + 2)" *)
evSS: "ev n ==> ev(Suc(Suc n))"


(* Rule Induction *)

(* 全ての偶数が特定の性質を有していることの証明が難しい例 *)

fun evn :: "nat => bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

(* prove ev m => evn m. 

これはRule Inductionの(帰納法を使うという意味で)特殊なケース

we want to prove a property P n for all even n. 
But if we assume ev n, then there must be some derivation of this assumption using the two defining rules for ev:
- Case ev0: P 0
- Case evSS: \<lbrakk> ev n; P n\<rbrakk> => P (n + 2)
.

これに該当するルールは、`ev.induct`と呼ばれ、以下のようなものである
  \<lbrakk> ev n, P 0, \<And> n. \<lbrakk> ev n ; P n \<rbrakk> ==> P(n + 2) \<rbrakk> ==> P n

`ev n`が前提に入っているのは、
- nがeven であることを知っている状態であることを要求している
  - これによって、evSSのruleの前提を簡単にする

帰納法の仮定がこの証明の全てにおいて要求しているわけではなく、
evSSのケースの処理において、ev nを持っていることが本質的である。

ルールのこのケース分析は "rule invension"と呼ばれ、chap 5で議論されている
*)


(* In Isabelle *)

(* recast the above informal proofs in Isabelle. *)
(* First, Suc terms instead of numerals in rule evSS *)

(* The simplest way to prove ev (Suc (Suc (Suc (Suc 0)))) is in a forward
direction: evSS[OF evSS[OF ev0]] yields the theorem ev (Suc (Suc (Suc(Suc 0)))). *)
lemma "ev(Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)
apply(rule evSS)
apply(rule ev0)
done

(* Rule induction is applied by giving the induction rule explicitly via the rule: modifier: *)
lemma "ev m ==> evn m"
apply(induction rule: ev.induct)
by(simp_all)

(* Note that if there are multiple assumptions of the form ev t, method induction will induct on the leftmost one. *)

lemma "evn n ==> ev n"
apply(induction n rule: evn.induct)
by(simp_all add: ev0 evSS)

(* 
`ev`のためのルールは、完璧な単純化と導入規則を作っている。
  なぜなら、それらの前提は常に結論より小さいから。
単純化と導入規則にそれらを永久的に変える場合に意味をなす
  証明の自動化をよりよくするために

Isabelleでは、 `ev.intros`と名付けられている。
*)
declare ev.intros[simp,intro]

(* 
帰納的な定義はデフォルトでは単純化規則ではない。
  なぜなら、再帰的な関数とは異なり、帰納的定義には決定性の条件がないから
*)

(* Inductive Versus Recursive *)

(* 
再帰的な方が便利ではある。
  項の中間を書ける
  何が正しいかというポジティブな情報と何が間違いかのネガティブな情報の両方を直接表現できる。

帰納的な方は、ポジティブな情報しか直接には表現しない。

Rule Induction はある証明にはよく合っている
  ポジティブなケースの証明のみを要求しているケース
    再帰的な方のinductで証明しようとすると、ネガティブなケースを明示的にしないといけない。

書き換えとRule Inductionの両方の恩恵を受けたいなら
  再帰的と帰納的の両方の二つの定義を書いて
    それらの等しさを示すか、
  新たに定義を作り
    そこから追加の性質を証明するか
*)

(* 
多くの概念は、再帰的定義を許容していない
  なぜなら再帰のためのdatatypeがないから

あと、再帰は止まらないかもしれない

再帰的な定義があったとしても、ポジティブな情報にしか興味がないなら、
帰納的定義の方がよりシンプルである。
*)

subsubsection "4.5.2 The Reflexive Transitive Closure"

(* 反射的で推移的閉包 `star` ：
  binary predicateを別のbinary predicateに変換する
*)

inductive star :: "('a => 'a => bool) => 'a => 'a => bool" for r where
refl: "star r x x" |
step: "r x y ==> star r y z ==> star r x z"

(* `for r` というのは、Isabelle に r は star において fixed parameter であることを教えるための者 *)

(* 推移的(transitive)であることの証明 *)
lemma star_trans: "star r x y ==> star r y z ==> star r x z"
apply(induction rule: star.induct)
(* autoを使わない理由は知らないが、多分、何を使うか分かり切っているからなのでは？ *)
apply(assumption)
(* sledgehammer *)
(* by (simp add: star.step) *)
(* テキストでmetisが使われているのは、straightforwarだから、と説明されている。 *)
by (metis step)

subsubsection "4.5.3 The General Case"

(* Inductive な定義は以下のような一般形式をたいていの場合持っている
  inductive I :: "t => bool" where
そして、それに続くルールは以下のような形式を持っている(n がゼロの場合もある)
  \<lbrakk> I a1; ... ; I an \<rbrakk> ==> I a
また、これらのルールは `|` でわけられている。

これに該当するrule induction は `I.induct` だり、これは、以下のような形式の命題に適用される
  I x ==> P x

Rule inductionは常にゴールの一番左のの前提に対してであり、よって、 `I x` は常に最初の前提でなければならない。

`I x ==> P x` をrule inductionによって証明するというのは、Iのすべての規則に対して、Pが不変であるということ、つまり
  \<lbrakk> I a1; P a1;... ; I an; P an \<rbrakk> ==> P a
*)

(* 
Iを含まないような追加の前提をもっているargumentsや規則をもっている場合がある
  これはside conditionsと呼ばれる
    これは追加の前提として表れることがある

`for` は反射的で推移的な閉包において、induction ruleを単純化するために用いられる。
*)

subsection "Exercises"

(* Exercise 4.2 *)
inductive palindrome :: "'a list => bool" where
"palindrome []" |
"palindrome [x]" |
"palindrome xs ==> palindrome (a # xs @ [a])"

lemma "palindrome xs ==> rev xs = xs"
apply(induction rule:palindrome.induct)
apply(auto)
done

(* Exercise 4.3. *)
inductive star' :: "( 'a => 'a => bool) => 'a => 'a => bool" for r where
refl' : "star' r x x" |
step' : "star' r x y ==> r y z ==> star' r x z"

lemma "star' r x y ==> star r x y"
apply(induction rule: star'.induct)
apply(rule refl)
 by (meson star.refl star.step star_trans)

(* cf: https://github.com/sergv/isabelle-playground/blob/master/Chapter4.thy *)

lemma star'_singleton : "r a b \<Longrightarrow> star' r a b"
by(metis step' refl')

(*  1. \<And>x. r x c \<Longrightarrow> star r x c *)
lemma ext_star'_from_left : "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
apply(induction rule: star'.induct)
apply(simp add:star'_singleton)
(* sledgehammer *)
by (meson step')

(*  1. \<And>x y z. r x y \<Longrightarrow> star r y z \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z *)
lemma "star r x y ==> star' r x y"
apply(induction rule: star.induct)
apply(rule refl')
apply(simp add: step ext_star'_from_left)
done

(* Exercise 4.4. *)
inductive iter :: "('a  => 'a => bool) => nat => 'a => 'a => bool" for r where
iter_refl: "iter r n x x" |
iter_step: "r x y ==> iter r n y z ==> iter r (Suc n) x z"

(* r y z ==> ...という形ではダメ。from: Rule inductionは常にゴールの一番左のの前提に対して *)
(* lemma ext_iter : "iter r n x y ==> r y z ==> iter r (Suc n) x z"
apply(induction rule:iter.induct)
apply() *)

(* 問で、nについての説明が一切ないので、存在することを示すことにした。 *)
(*  1. \<And>x y z. r x y \<Longrightarrow> star r y z \<Longrightarrow> iter r n y z \<Longrightarrow> iter r n x z *)
lemma "star r x y ==> \<exists> n. iter r n x y"
apply(induction rule: star.induct)
apply(metis iter_refl)
(* sledgehammer *)
by (meson iter_step)

(* Exercise 4.5. *)

datatype alpha = a | b

inductive S :: "alpha list => bool" where
SEmpty: "S[]" |
SConct: "S w ==> S (a # w @ [b])" |
SDoubl: "S w1 ==> S w2 ==> S (w1@w2)"

inductive T :: "alpha list => bool" where
emptyT: "T[]" |
balanceT: "T w1 ==> T w2 ==> T(w1@[a]@w2@[b])"

lemma TtoS: "T w ==> S w"
apply(induction rule: T.induct)
apply(rule S.SEmpty)
by (simp add: SConct SDoubl)

(* cf: https://github.com/sergv/isabelle-playground/blob/master/Chapter4.thy *)
(* この道具を使わないと、とても面倒な証明が要求されてしまう *)
thm balanceT[OF emptyT]
lemmas balanceT' = balanceT[OF emptyT, simplified]

lemma balance_composite_first: "T (w1 @ w2) ==> T w3 ==>  T (w1 @ w2 @ [a] @ w3 @ [b])"
apply(simp)
apply(rule balanceT[of "w1 @ w2" w3, simplified])
(* sledgehammer *)
apply(auto)
done

(*  1. \<And>w1 w2a.
       T w1 \<Longrightarrow>
       T (w1 @ w2) \<Longrightarrow> T w2a \<Longrightarrow> T (w2a @ w2) \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ a # w2a @ b # w2) *)
lemma composite_T : "T w2 ==> T w1 ==> T (w1 @ w2)"
apply(induction arbitrary: w1 rule: T.induct)
apply(simp)
(* sledgehammer *)
using balance_composite_first by auto

(* 1. \<And>w1 w2. S w1 \<Longrightarrow> T w1 \<Longrightarrow> S w2 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ w2) *)
lemma StoT: "S w ==> T w"
apply(induction rule: S.induct)
apply(rule emptyT)
using balanceT emptyT apply fastforce
(* sledgehammer *)
by (simp add: composite_T)


end