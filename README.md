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
