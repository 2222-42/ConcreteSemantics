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

end