theory ConcreteSemantics5
  imports Main
begin

section "4 Isar: A Language for Structured Proofs"

(* 
apply-scriptsだと読みづらいし、保守しづらい。
    アセンブリ言語感がある
より大きな証明のための言語の選択はIsar。
    コメントを含む構造化されたプログラム感がある

*)

(* Isarの特徴:
- 構造化されたもの、線形ではない
- 走らせずとも読むことができる。なぜなら、任意の与えられた場所で何を証明しているのか述べなければならないから。
*)

(* Isarの証明の形:

以下によって、 `f_0 ==> f_{n+1}`を証明する。
```
proof
    asume f_0
    have f_1
    ...
    have f_n
    show f_{n+1} 
qed
```
- `have` は進めるための踏み石
- `show` は実際のゴールを証明するもの
*)

(* Isarのcore syntax:

[証明を担当する部分]
proof = by method
      | proof [method] step* qed

`proof - qed`ブロックで、複数のステップをやる。
    `induction xs`などのproof methodから始めることもできる。

[命題を仮定するか証明に付け加える命題を述べる]
step = fix variables
     | assume proposition
     | [from fact+] (have | show) proposition proof

- from: 証明で使う事実(facts)を述べる
- have: 中間の命題を述べる
- show: 全体のゴールを述べる
- fix: 新たなローカル変数の導入
  - 論理的には、\<And> - 量化された変数の導入
- assume: 含意(`==>`)の仮定を導入する。
  - have/showで含意の結論を導く
  
proposition = [name:] "formula"

fact = name | ...

- propositions はオプションで名付けられた式のこと。
  - この名前は`from`で言及可能なものである。
- facts はpropositionであると同時に `OF` や `of` で構成されるものに使える
  - factの... にはlemma なども入る。
    - これらはまとめて`facts`として言及される。
  - factはfactsのリストの代わりとなる
    - e.g., `f.simps` は`f`の再帰的な等式のリストに言及している
      - `f.simps(2)` や `f.simps(2-4)`

*)

subsection "5.1 Isar by Example"

(* proofs of Cantor’s theorem that a function from a set to its powerset cannot be surjective *)
lemma "\<not> surj (f :: 'a => 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists> a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

(* 意味ある名づけは作るの難しいし大半の場合必須ではない *)

subsubsection "5.1.1 this, then, hence and thus"

(* labesは避けるべき。読者の流れを邪魔する *)
(* 証明は線形順序である *)
(* `this` は前のステップで証明された命題を示す *)
(* これによって証明がシンプルになる *)

lemma "\<not> surj (f :: 'a => 'a set)"
proof
  assume "surj f"
  from this have "\<exists> a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  from this show "False" by blast
qed

(* 
略称がある
- then = from this
- thus = then show = from this show
- hence = then have = from this have
*)

lemma "\<not> surj (f :: 'a => 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  thus "False" by blast
qed

(* 他のバリエーションについて
- (have | show) prop using facts = from facts (have | show) prop
- with facts = from facts this

`using` は、proposition の後ろに facts を動かすことで、facts を強調しなくする
*)

subsubsection "5.1.2 Structured Lemma Statements: fixes, assumes, shows"

(* lemma はもっと構造化された流儀で述べることができる *)
lemma 
  fixes f :: "'a => 'a set"
  assumes s: "surj f"
  shows "False"
(* 
- fixes part: 
  - 変数の型を前もって述べることができる
    - 式の中に表れるものを型制約でデコレートするのではなく
- assumes part;
  - それぞれの仮定に名前を付けること
    - これが構造化された形式におけるキーとなる利点である
    - 他のfact同様に、個の名前は証明のなかで使える
  - 複数の仮定は`and`によって分けることができる
- shows part;
  - ゴールを与える
*)
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by (auto simp: surj_def)
  thus "False" by blast
qed
(* 
`proof` コマンドの後のハイフン `-` について
  これは、null method
    ゴールに対して何もしていない
    goalに至るための適切な導入規則を試すことをisabelleにお願いしない
*)

(* 
「`surj f`の重複は、削除される」これがどういう意味かよくわからない。
The duplication of surj f in the above proofs (once in the statement of the lemma,
once in its proof) has been eliminated
*)

(* 
assumes-showsの形で述べられたlemmaは
すべてのassumptionのリストの代わりをなす名前`assms`を暗黙的に導入する
  `assms(1)`や `asms(2)`などの形で、個々の仮定に言及できる。
    よって、名付けることの必要性を除く。
*)

subsection "5.2 Proof Patterns"

(* case analysis: 
proof cases
  これで排中律を使って証明している
*)

(* contradiction
proof (rule ccontr)
  これで二重否定除去則を使って証明
*)

(* quantified formulas:
the step fix x introduces a locally fixed variable
-> これで任意のxについて成り立つことを示す

witness is some arbitrary term for which we can prove that it satisfies P.
-> 一個でも見つけられればいいのだから
*)

(* 量化子からの導出・推論の仕方
obtain stepでfiexed local variableを取ろう。
*)

lemma "\<not> surj (f :: 'a => 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast 
  thus "False" by blast
qed

(* 等式と包含関係の証明 *)


subsection "5.3 Streamlining Proofs"

subsubsection "5.3.1 Pattern Matching and Quotations"

(* 式が重複している場合がある。これは可読性も、書きやすさも、保守しやすさも悪くなる 
-> パターンマッチングを使おう

show formula (is pattern)
  この式が述べられている任意の場所でパターンマッチングは昨日する

e.g., show "formula1 \<longleftrightarrow> formula2" (is "?L  \<longleftrightarrow> ?R")
  こうすると、後に続く証明の中で、 "?L" "?R"が代わりに使えるようになる。

e.g., show ?thesis
  ?thesis は lemma や show で述べられた任意のゴールに暗黙的にマッチするものである。

e.g., let ?t = "some-big-term"
  unknowns も let でインスタンス化できる
  こうすると後の証明ステップで ?t に言及することができる
    e.g., have "... ?t ..."

補足: 
- factsの名前は、証明された定理に言及する
- unknowsn ?Xは、項や式に言及する
*)

(* 名前は分かりやすくしような。長くてもいいから。 *)

(* 
have "x > 0"
...
from ‘x>0‘ . . .

back quotesは、名前によってではなく、値によって、factに言及している。
*)


subsubsection "5.3.2 moreover"

(* moreover: factになんらかの演繹をできるようにさせたい場合に使う

e.g.,

have lab1: "P1" <proof>
have lab2: "P2" <proof>
...
have labn: "Pn" <proof>
from lab1 lab2 ...
have "P" <proof>
という感じで、facts にラベル付けて、ではなく

have "P1" <proof>
moreover have "P2" <proof>
moreover
...
moreover have "Pn" <proof>
ultimately have "P" <proof>

moreoverでこれらをつなげて証明する。
  短くなるわけではないが、もうちょっと明快に構造を明らかにし、新たな名前を作るのを避けてくれる
*)


subsubsection "5.3.3 Local Lemmas"

(* 
証明の中でなんらかの補題を証明したい場合
  仮定の現在のコンテキストを共有する補題
  だが、独自の仮定を持っており、そして最後にはローカルに固定された変数に関して一般化されているような補題
  `have`の拡張

    have B if name: A1 ... Am for x1 ... xn
    <proof>
*)

thm dvd_def

lemma fixes a b :: int assumes "b dvd (a + b)" shows "b dvd a"
proof - 
  have "\<exists> k'. a = b * k'" if asm: "a + b = b * k" for k
  proof
    show "a = b*(k-1)" using int_distrib(4) that by auto
  qed
  thus ?thesis using assms by auto
qed

subsubsection "Exercises"

(* Exercise 5.1 *)
lemma assumes T: "\<forall> x y. T x y \<or> T y x"
and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof -
have "T x y \<or> \<not> T x y" by simp
then show "T x y"
proof
  assume "T x y"
  then show "T x y" by simp
next
  assume "\<not> T x y"
  from this have "T y x" using T by blast
  from this have "A y x" using TA by blast
  from this have "x = y" using A assms(4) by blast
  then show "T x y" using \<open>T y x\<close> by auto
qed
qed

(* Exercise 5.2 *)
lemma "\<exists> ys zs. xs = ys @ zs \<and> 
        ( length ys = length zs \<or>  length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
  then obtain a where "length xs = 2 * a" by auto
    let ?ys = "take a xs"
    let ?zs = "drop a xs"
    have "xs = ?ys @ ?zs \<and>length ?ys = length ?zs" by(simp add: `length xs = 2 * a`)
    hence "xs = ?ys @ ?zs \<and>
        (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by (auto)
    thus ?thesis by blast
next
  assume "odd (length xs)"
  then obtain a where "length xs = (2 * a) + 1" 
    using oddE by blast
    let ?ys = "take (a + 1) xs"
    let ?zs = "drop (a + 1) xs"
    have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by (simp add: \<open>length xs = 2 * a + 1\<close>)
    hence "xs = ?ys @ ?zs \<and>
        (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by (auto)
    thus ?thesis  by blast
qed


subsection "5.4 Case Analysis and Induction"

subsubsection "5.4.1 Datatype Case Analysis"

(* 前節ではformulasに対するケース分析だった。本節では、項の形式に関する分析 *)

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  then show ?thesis by simp
next
  fix y ys assume "xs = y # ys"
  then show ?thesis by simp
qed

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis by simp
qed

subsubsection "5.4.2 Structural Induction"

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof(induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof(induction n)
  show "?P 0" by simp
next 
  fix n assume "?P n"
  then show "?P (Suc n)" by simp
qed

subsubsection "5.4.3 Rule Induction"

inductive ev :: "nat => bool" where
ev0: "ev 0"|
evSS: "ev n ==> ev(Suc(Suc n))"

fun evn :: "nat => bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev n ==> evn n"
proof(induction rule: ev.induct)
  case ev0
  then show ?case by simp
next
  case evSS 
  then show ?case by simp
qed

(* case of referring to m *)
lemma "ev n ==> evn n"
proof(induction rule: ev.induct)
  case ev0 show ?case by simp
next
  case (evSS m)
  have "evn(Suc(Suc m)) = evn m" by simp
  thus ?case by (simp add: evSS.IH)
  (* thus ?case by simp *)
qed

subsubsection "5.4.4 Assumption Naming"

subsubsection "5.4.5 Rule Inversion"

(* 何かのfactを導くのに使われうるような規則の分析 *)
(* 逆向きの証明：
いずれのルールによって、与えられた事実が証明しうるか？
e.g.,
  ev n ==> n = 0 \<or> (\<exists> k. n = Suc (Suc k) \<and> ev k)
*)

(* assume "ev n"
from this have "ev(n-2)"
proof cases
  case ev0 thus ?thesis by (simp add: ev.ev0)
next
  case (evSS k) thus ?thesis by (simp add: ev.evSS)
qed *)

(* some rules could not have been used to derive the given fact
because constructors clash *)
(* Impossible cases do not have to be proved.
  assume "ev(Suc 0)" then have P by cases
*)
lemma "\<not> ev(Suc 0)"
proof
assume "ev(Suc 0)" then show False by cases
qed

subsubsection "5.4.6 Advanced Rule Induction"

(* `I r s t ==> ...`で、r, s, tが変数ではない場合、証明することができない。
どうするか。
`"I x y z ==> x = r ==> y = s ==> z = t ==> ..."`
として、新たな変数x, y, zを導入して、標準的な形式にする。

proof(induction "r" "s" "t" arbitrary: ... rule: I.induct)
*)

lemma "ev(Suc m) ==> \<not> ev m"
proof(induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And> m. n = Suc m ==> \<not> ev m"
  (* `ev x ==> x = Suc m ==> \<not> ev m` に至るように拡張されている *)
  show "\<not> ev (Suc n)"
  proof 
  (* using contradiction *)
    assume "ev(Suc n)"
    thus False
    proof cases
    (* using rule inversion *)
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed


subsubsection "Exercise"

(* Exercise 5.3. *)
(* Give a structured proof by rule inversion: *)
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
proof -
  (* assume "ev m"
  from this a have "ev (m -2)"
  proof cases
    case ev0
    then show ?thesis by (simp add: ev.ev0)
  next
    case (evSS k)
    then show ?thesis by (simp add: ev.evSS)
  qed *)
  from a show ?thesis by cases
qed

(* Exercise 5.4. *)
lemma "\<not> ev(Suc(Suc(Suc 0)))"
proof
  assume "ev(Suc(Suc(Suc 0)))" 
  then show False
  proof cases
    assume "ev(Suc 0)" thus ?thesis by cases
  qed
qed

(* Exercise 5.5. *)
inductive star :: "('a => 'a => bool) => 'a => 'a => bool" for r where
refl: "star r x x" |
step: "r x y ==> star r y z ==> star r x z"

inductive iter :: "('a  => 'a => bool) => nat => 'a => 'a => bool" for r where
iter_refl: "iter r n x x" |
iter_step: "r x y ==> iter r n y z ==> iter r (Suc n) x z"

lemma "iter r n x y ==> star r x y"
proof(induction rule: iter.induct)
  case (iter_refl n x)
  then show ?case by (simp add:star.refl)
next
  case (iter_step x y n z)
  then show ?case by (simp add: star.step)
qed

(* Exercise 5.6 *)
fun elems :: "'a list => 'a set" where
"elems [] = {}" |
"elems (x#xs) = {x} \<union> elems xs"

lemma "elems [1,2,3,(4::nat)] = {1,2,3,4}" (*<*)by auto(*>*)

(* elems is recursive function *)
lemma "x \<in> elems xs ==> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" (is "?A ==> ?B")
(* proof (induction xs rule: elems.induct) *)

proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
  proof cases
    assume x_is_a: "x = a"
    then obtain zs where "x#zs = a#xs" by blast
    let ?ys = "[]"
    have "x \<notin> elems ?ys" by simp
    then show ?thesis using x_is_a by blast
  next
    assume x_is_not_a: "x \<noteq> a"
    from Cons this obtain ys zs where ys: "xs = ys @ x # zs" "x \<notin> elems ys" by auto
    show ?thesis 
    proof
      show "\<exists>zs. a # xs = (a # ys) @ x # zs \<and> x \<notin> elems (a # ys)"
        using ys x_is_not_a by simp
    qed
  qed
qed

(* Exercise 5.7. *)
datatype alpha = a | b

inductive S :: "alpha list => bool" where
SEmpty: "S[]" |
SConct: "S w ==> S (a # w @ [b])" |
SDoubl: "S w1 ==> S w2 ==> S (w1@w2)"

inductive T :: "alpha list => bool" where
emptyT: "T[]" |
balanceT: "T w1 ==> T w2 ==> T(w1@[a]@w2@[b])"

fun balanced :: "nat => alpha list => bool" where
"balanced 0 [] = True" |
"balanced n (a#xs) = balanced (Suc n) xs" |
"balanced (Suc n) (b # xs) = balanced n xs" |
"balanced _ _ = False"

lemma [simp]: "balanced n w ==> balanced (Suc n) (w @ [b])"
apply (induct n w rule: balanced.induct)
apply simp_all
done

lemma [simp]: "\<lbrakk> balanced n v; balanced 0 w \<rbrakk> \<Longrightarrow> balanced n (v @ w) "
apply (induct n v rule: balanced.induct)
apply simp_all
done

(* value "replicate 3 a" *)

lemma "S w ==> balanced 0 w"
apply(erule S.induct)
apply(simp_all)
done

lemma [iff]: "S[a,b]"
using SConct[where w = "[]"] by (simp add: SEmpty)

lemma ab: 
  assumes u: "S u"
  shows "\<And> v w. u = v @ w ==> S(v @ a # b # w)"
using u
proof(induct)
  case SEmpty
  then show ?case by simp
next
  case (SConct w)
  have Su:"S u" and
       IH: "\<And> v w. u = v @ w ==> S(v @ a # b # w)" and
       asm: "a # u @ [b] = v @ w" sorry
  show "S(v @ a # b # w)" sorry
next
  case (SDoubl w1 w2)
  then show ?case sorry
qed

lemma
  "balanced n w ==> S (replicate n a @ w)"
apply(induct n w rule: balanced.induct)
apply(simp_all)
apply (simp add: SEmpty)
apply(simp add: replicate_app_Cons_same)
by (metis ab replicate_app_Cons_same)

(* proof (induction n w rule: balanced.induct)
  case 1
  then show ?case  by (simp add: SEmpty) 
next
  case (2 n xs)
  then show ?case by (simp add: replicate_app_Cons_same)
next
  case (3 n xs)
  then show ?case sledgehammer
next
  case ("4_1" v)
  then show ?case sorry
next
  case ("4_2" va)
  then show ?case sorry
qed *)


end