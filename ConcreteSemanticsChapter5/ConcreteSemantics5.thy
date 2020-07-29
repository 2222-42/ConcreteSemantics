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

end