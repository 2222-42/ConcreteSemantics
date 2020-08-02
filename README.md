# ConcreteSemantics 

2222-42のIsabelle勉強ノート

## text

[Concrete Semantics](http://www.concrete-semantics.org/index.html)を読んでいる

## Memo

addとintroの区別
- `add`はadditional lemmaを追加。(最も左のものに適用させる)
- `intro`はintroduction ruleを追加
- `rule`はRule Applicationを適用すること(backwards)

`arbitrary` は `rule` の前に書く必要がある

simpかautoか
- `auto`はsimplificationをやって、それに対して全部のサブゴールに対して自動で適用させる。
- `simp`はsimplificationだけをやってくれるから、autoが実行数量なのが必要なければやらない方がらく。

Introduction Rule:
- 導入規則は、どの前提によって、論理構成子が導入されたのかを説明する。
- 定理`r`があったら、`r [of f1 ... f2]`によって、そのunknownsを埋めることができる。
- 定理`r`があったら、`r [OF r1 ... rm]`によって、導入規則を作れる

fastforceについて
- 最初のsubgoalについてのみ実施する。
- slow versionのforceでは成功するが、fastforceでは失敗することがある

blast:
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

### Isar

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

#### core syntax

[証明を担当する部分]
```
proof = by method
      | proof [method] step* qed
```

`proof - qed`ブロックで、複数のステップをやる。
    `induction xs`などのproof methodから始めることもできる。

[命題を仮定するか証明に付け加える命題を述べる]
```
step = fix variables
     | assume proposition
     | [from fact+] (have | show) proposition proof
```

- from: 証明で使う事実(facts)を述べる
- have: 中間の命題を述べる
- show: 全体のゴールを述べる
- fix: 新たなローカル変数の導入
  - 論理的には、\<And> - 量化された変数の導入
- assume: 含意(`==>`)の仮定を導入する。
  - have/showで含意の結論を導く

```
proposition = [name:] "formula"
```

```
fact = name | ...
```

- propositions はオプションで名付けられた式のこと。
  - この名前は`from`で言及可能なものである。
- facts はpropositionであると同時に `OF` や `of` で構成されるものに使える
  - factの... にはlemma なども入る。
    - これらはまとめて`facts`として言及される。
  - factはfactsのリストの代わりとなる
    - e.g., `f.simps` は`f`の再帰的な等式のリストに言及している
      - `f.simps(2)` や `f.simps(2-4)`

#### abbreviation

略称がある
- then = from this
- thus = then show = from this show
- hence = then have = from this have

#### variations

他のバリエーションについて
- (have | show) prop using facts = from facts (have | show) prop
- with facts = from facts this

`using` は、proposition の後ろに facts を動かすことで、facts を強調しなくする

#### fixes

- fixes part: 
  - 変数の型を前もって述べることができる
    - 式の中に表れるものを型制約でデコレートするのではなく
- assumes part:
  - それぞれの仮定に名前を付けること
    - これが構造化された形式におけるキーとなる利点である
    - 他のfact同様に、個の名前は証明のなかで使える
  - 複数の仮定は`and`によって分けることができる
- shows part:
  - ゴールを与える

### proof-patterns

proof cases:
- これで排中律を使って証明している

proof (rule ccontr):
- これで二重否定除去則を使って証明

quantified formulas:
- the step fix x introduces a locally fixed variable
  - -> これで任意のxについて成り立つことを示す
- witness is some arbitrary term for which we can prove that it satisfies P.
  - -> 一個でも見つけられればいいのだから

量化子からの導出・推論の仕方:
- obtain stepでfiexed local variableを取ろう。

### pattern-matching

式が重複している場合がある。これは可読性も、書きやすさも、保守しやすさも悪くなる 
-> パターンマッチングを使おう

`show formula (is pattern)`
  この式が述べられている任意の場所でパターンマッチングは昨日する

e.g., `show "formula1 \<longleftrightarrow> formula2" (is "?L  \<longleftrightarrow> ?R")`
  こうすると、後に続く証明の中で、 "?L" "?R"が代わりに使えるようになる。

e.g., `show ?thesis`
  ?thesis は lemma や show で述べられた任意のゴールに暗黙的にマッチするものである。

e.g., `let ?t = "some-big-term"`
  unknowns も let でインスタンス化できる
  こうすると後の証明ステップで ?t に言及することができる
    e.g., `have "... ?t ..."`

#### fix 

特定の条件を含めた変数を取りたいなら、
fixじゃなくてletの方がいいと思った。
  fixでも`fix y ys assume "xs = y#ys"`として導入できるじゃん。

### moreover
```
have lab1: "P1" <proof>
have lab2: "P2" <proof>
...
have labn: "Pn" <proof>
from lab1 lab2 ...
have "P" <proof>
```
という感じで、facts にラベル付けて、ではなく

```
have "P1" <proof>
moreover have "P2" <proof>
moreover
...
moreover have "Pn" <proof>
ultimately have "P" <proof>
```

### Datatype case analysis

```
proof (cases xs)
```

datatypeの構成子`C`に対して、
```
fix x 1 ... x n assume "t = C x 1 ... x n"
```
もしくは
```
case (C x 1 ... x n)
```
、それぞれについて証明されることが、datatypeの証明のパターンである。

#### Structural induction case

```
proof (induction n)
  case 0
  ...
  show ?case hproof i
next
  case (Suc n)
  ...
  show ?case hproof i
qed
```

`case 0`でやっていることは`let ?case = "P(0)"`であり、
`case (Suc n)`でやっていることは
- `fix n assume Suc: "P(n)"`
- `let ?case = "P(Suc n)"`

command `case (C x1 ... xn)`が実行していること
1. `fix x 1 ... x n`
2. `assume` the induction hypotheses ( `C.IH` と呼ばれる) と the premises　`A_i(C x 1 ... x n)` ( `C.prems`と呼ばれる) and calling the whole list C
3. `let ?case = "P(C x 1 ... x n)"`

#### Rule Induction case

Structural Inductionとは異なりRule Induction は、
- 明示的に与えられ
- ケースの名前は帰納的定義におけるルールの名前が使われうる


Rule Inductinによる証明のパターンは以下の通り:
```
show "I x =) P x"
proof(induction rule: I.induct)
  case rule_1 ...
  show ?case <proof>
next
...
next 
  case (rule_i x 1 ... x k)
  show ?case <proof>
...
next
  case rule_n ...
  show ?case <proof>
qed
```

rule iに対して自由変数を左から順に明示的に当てることもできる
