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

lemma balanced_wrap [simp]: "balanced n w ==> balanced (Suc n) (w @ [b])"
apply (induct n w rule: balanced.induct)
apply simp_all
done

lemma balanced_concat[simp]: "\<lbrakk> balanced n v; balanced 0 w \<rbrakk> \<Longrightarrow> balanced n (v @ w) "
apply (induct n v rule: balanced.induct)
apply simp_all
done

(* value "replicate 3 a" *)
(* cf: https://isabelle.in.tum.de/exercises/logic/parentheses/sol.pdf *)
lemma [simp]: "S w ==> balanced 0 w"
apply(erule S.induct)
apply(simp_all)
done

lemma [iff]: "S[a,b]"
using SConct[where w = "[]"] by (simp add: SEmpty)

lemma replicate_split: "m < n \<Longrightarrow> replicate n x = replicate m x @ replicate (n - m) x"
  by (metis add_diff_inverse_nat less_imp_not_less replicate_add)

lemma append_split: "length cs < length as \<Longrightarrow> as @ bs = cs @ ds \<Longrightarrow> \<exists>es. as = cs @ es"
  by (metis add_diff_inverse_nat append_Nil2 append_eq_append_conv_if
            drop_all length_drop less_imp_not_less)
lemma ab: 
  assumes u: "S u"
  shows "\<And> v w. u = v @ w ==> S(v @ a # b # w)"
using u
proof(induct)
  case SEmpty
  then show ?case by simp
next
  case (SConct u)
  have Su:"S u" and
       IH: "\<And> v w. u = v @ w ==> S(v @ a # b # w)" and
       asm: "a # u @ [b] = v @ w" by fact+
  show "S(v @ a # b # w)" 
  proof (cases v)
    case Nil
    hence "w = a # u @ [b]" using asm by simp
    hence "S w" by (simp add: S.SConct Su)
    hence "S ([a,b]@w)" using SDoubl by blast
    then show ?thesis  by (simp add: local.Nil)
  next
    case (Cons x v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      (* w = [] \<Longrightarrow> S (v @ a # b # w) *)
      (* v = (a # u @ [b]) , w = [] *)
      from Su have "S ((a # u @ [b]) @ [a, b])" using S.SConct SDoubl by blast
      then show ?thesis by (simp add: asm local.Nil)
    next
      case (snoc w' y)
      hence u: "u = v' @ w'" and [simp]: "x = a & y = b" using asm local.Cons by auto
      from u have "S(v' @ a # b # w')" by(rule IH)
      hence "S(a # (v' @ a # b # w') @ [b])" using S.SConct by blast
      then show ?thesis by (simp add: local.Cons snoc)
    qed
  qed
next
  case (SDoubl v' w')
  have Sv': "S v'" and Sw': "S w'"
   and IHv: "\<And> v w. v' = v @ w ==> S(v @ a # b # w)"
   and IHw: "\<And> v w. w' = v @ w ==> S(v @ a # b # w)"
   and asm: "v' @ w' = v @ w" by fact+
  then obtain r where "v' = v @ r \<and> r @ w' = w \<or> v' @ r = v \<and> w' = r @ w" (is "?A \<or> ?B") by (meson append_eq_append_conv2)
  thus ?case 
  proof
    assume A: ?A
    hence "S(v @ a # b # r)" using IHv by simp
    hence "S((v @ a # b # r) @ w')" using Sw' using S.SDoubl by blast
    thus ?thesis using A by auto
  next
    assume B: ?B
    hence "S(r @ a # b # w)" using IHw by blast
    hence "S(v' @ (r @ a # b # w))" using Sv' using S.SDoubl by blast
    thus ?thesis using B by auto
  qed
qed

lemma b_to_s:
  "balanced n w ==> S (replicate n a @ w)"
apply(induct n w rule: balanced.induct)
apply(simp_all)
apply (simp add: SEmpty)
apply(simp add: replicate_app_Cons_same)
by (metis ab replicate_app_Cons_same)

(* lemma "S (b # va) \<Longrightarrow> \<not> balanced 0 va"
sledgehammer *)

(* lemma "S (replicate n a @ w) ==> balanced n w"
apply(induct n w rule: balanced.induct)
apply(simp_all)
apply(simp add: replicate_app_Cons_same)
sorry *)

(* lemma 
  fixes v
  assumes "S v"
  shows "\<And>n w. (v = replicate n a @ w) \<Longrightarrow> balanced n w"
proof (induct)
  case a
  fix n w
  (* \<And>n w. v = replicate n a @ w \<Longrightarrow> balanced n w *)
  then show ?case sorry
next
  case b
  (* \<And>n w. v = replicate n b @ w \<Longrightarrow> balanced n w *)
  then show ?case sorry
qed *)

lemma s_to_b:
  fixes n w
  assumes Sv: "S v"
  shows "\<And>n w. (v = replicate n a @ w) \<Longrightarrow> balanced n w"
using Sv
proof (induct)
  case SEmpty
  then show ?case by auto
next
  case (SConct u)
  (* \<And>w n wa.
       S w \<Longrightarrow>
       (\<And>n wa. w = replicate n a @ wa \<Longrightarrow> balanced n wa) \<Longrightarrow>
       a # w @ [b] = replicate n a @ wa \<Longrightarrow> balanced n wa *)
  have Su: "S u"
   and IH: "\<And> n w. u = replicate n a @ w \<Longrightarrow> balanced n w"
   and asm: "a # u @ [b] = replicate n a @ w" by fact+
  show "balanced n w" 
  proof (cases n)
    case 0
    have "balanced 0 u" using IH by auto
    then show "balanced n w" using "0" asm by auto
  next
    case (Suc nat)
    then obtain y where "y @ [b] = w" using asm by (metis alpha.distinct(1) append_Cons append_Nil2 append_butlast_last_id last_appendR last_replicate last_snoc nat.distinct(1)) 
    then have "u = replicate nat a @ y" using asm using Suc by auto
    then have "balanced nat y" using IH by blast
    then show ?thesis using Suc \<open>y @ [b] = w\<close> balanced_wrap by blast
  qed
  (* proof (cases w rule:rev_cases)  
    case Nil
    then show ?thesis by (metis Nil_is_append_conv alpha.distinct(1) append_self_conv asm empty_replicate last_ConsR last_replicate last_snoc list.discI)
  next
    case (snoc ys y)
    (* hence "S (replicate n a @ ys @ [y])" sorry *)
    (* hence "balanced n ys" sledgehammer *)
    hence u: "u = replicate n a @ ys" sorry
    have "balanced n ((a # b # ys) @ [b])" using asm snoc u by auto
    then show ?thesis  using asm snoc by auto
  qed *)

next
  case (SDoubl w1 w2)
  have Sw1: "S w1" and Sw2: "S w2"
   and IHw1: "\<And>n w. w1 = replicate n a @ w \<Longrightarrow> balanced n w"
   and IHw2: "\<And>n w. w2 = replicate n a @ w \<Longrightarrow> balanced n w"
   and assm: "w1 @ w2 = replicate n a @ w" by fact+
  then have "w1 = [] \<or> w1 \<noteq> []" by simp
  then show "balanced n w" 
  proof 
    assume w1_is_nil: "w1 = []"
    show "balanced n w" using IHw2 w1_is_nil assm by auto
  next
    assume w1_is_not_nil: "w1 \<noteq> []"
    show "balanced n w" 
    proof cases
      (* impossible case *)
      assume "n > length w1"
      then have "w1 @ w2 = replicate (length w1) a @ replicate (n - length w1) a @ w" by (simp add: assm replicate_split)
      then have "w1 = replicate (length w1) a" by simp
      then have False using w1_is_not_nil by (metis IHw1 append.right_neutral balanced.simps(4) gr0_implies_Suc linorder_neqE_nat not_less0 replicate_empty)
      show "balanced n w" by (metis IHw1 \<open>w1 = replicate (length w1) a\<close> append_Nil2 balanced.simps(4) gr0_conv_Suc linorder_neqE_nat not_less0 replicate_empty w1_is_not_nil)
    next
      assume "\<not> (n > length w1)"
      then obtain z where z: "w1 = replicate n a @ z" using assm append_split by (metis append.right_neutral append_eq_append_conv length_replicate linorder_neqE_nat)
      then have left: "balanced n z" using IHw1 by blast
      have right: "balanced 0 w2" using IHw2 by simp
      have w: "w = z @ w2" using z assm by simp
      from left right w show "balanced n w" using balanced_concat by simp
    qed
  qed
qed

(* 
proof (cases w)
    case Nil
    (* hence "w = a # u @ [b]" using asm by simp
    hence "S w" by (simp add: S.SConct Su)
    hence "S ([a,b]@w)" using SDoubl by blast *)
    then show ?thesis  by (metis Nil_is_append_conv alpha.distinct(1) append_Nil2 asm empty_replicate last_ConsR last_replicate last_snoc list.discI)
  next
    case (Cons x v')
    (* w = x # v' *)
    (* 
    "a # u @ [b] = replicate n a @ w"
    "a # u @ [b] = replicate n a @ x # v'"
    *)
    (* have sub: "S(replicate n a @ x # v')" using S.SConct Su asm local.Cons by fastforce
    then have u: "a # u @ [b] = replicate n a @ x # v'" using asm local.Cons by blast *)
    have "u = replicate n a @ v'" sledgehammer
    then have "balanced n w" by (rule IH)
    then show ?thesis sledgehammer
    (* proof -


      (* have "S(w)" using "0" S.SConct asm Su by auto *)
      have "a # u @ [b] = replicate n a @ w" by (simp add: asm)
      have "S(a # u @ [b])" by (simp add: S.SConct Su)
      hence "balanced n w" by (rule IH)
      (* hence "u = replicate n a @ w ==> balanced n w" using IH by blast  *)
      
      then show "balanced n w" sorry
       (*balanced n w  *)
      (* then show ?thesis sorry *)
    (* next
      case (Suc nat)
      then show ?thesis sorry *)
    qed *)
  qed
*)

(* lemma "S(replicate n a @ w) \<Longrightarrow> balanced n w"
(* lemma 
  fixes v
  assumes Sv: "S v"
  shows "\<And>n w. (v = replicate n a @ w) \<Longrightarrow> balanced n w" *)
proof (induction rule: S.induct)
  case SEmpty
  then show ?case sorry
next
  case (SConct w)
  then show ?case sorry
next
  case (SDoubl w1 w2)
  then show ?case sorry
qed *)
(* 
lemma "S(replicate n a @ w) \<Longrightarrow> balanced n w"
proof(induction n w rule: balanced.induct)
  case 1
  then show ?case by simp
next
  case (2 n xs)
  then show ?case by (simp add: replicate_app_Cons_same) 
next
  case (3 n xs)
  (* \<And>n xs.
       (S (replicate n a @ xs) \<Longrightarrow> balanced n xs) \<Longrightarrow>
       S (replicate (Suc n) a @ b # xs) \<Longrightarrow> balanced (Suc n) (b # xs) *)
  have IH: "S (replicate n a @ xs) \<Longrightarrow> balanced n xs"
   and asm: "S (replicate (Suc n) a @ b # xs)" by fact+
  (* hence "S(replicate n a @ xs)" and "S(replicate 1 a @ [b])" sledgehammer *)
  then show "balanced (Suc n) (b # xs)" sorry
next
  case ("4_1" v)
  (* \<And>v. S (replicate (Suc v) a @ []) \<Longrightarrow> balanced (Suc v) [] *)
  have asm: "S (replicate (Suc v) a @ []) " by fact+
  
  then show "balanced (Suc v) []" sorry
next
  case ("4_2" va)
  (* \<And>va. S (replicate 0 a @ b # va) \<Longrightarrow> balanced 0 (b # va) *)
  have asm: "S (replicate 0 a @ b # va)" by fact+
  
  show "balanced 0 (b # va)" sorry
qed
*)

theorem "balanced n w = S (replicate n a @ w)" (is "?L = ?R")
proof
show "?L ==> ?R" by (simp add: b_to_s)
next
show "?R ==> ?L" by (simp add: s_to_b)
qed

end