/-!
# Lean で学ぶ初めての整数論

定理証明支援系 Lean を使って，整数論を学んでいこうという本です．

Lean の解説ではなく数学の解説を目的としているため，読者が Lean にある程度慣れていることを仮定しています．

## 本書の読む際の注意

本書のすべての Lean コードブロックには Lean Playground へジャンプするボタンが搭載されています．しかし必要な `import` 文などが含まれていないため，ほとんどの場合そのままでは動かないと思います．

右上にある実行ボタン <i class="fa fa-play"></i> をクリックすると，Playground でソースコードを実行することができます．

## リンク集

無料で閲覧できるものに限定して，参考になりそうな資料を紹介します．Lean については，次のようなものがあります．

* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) Lean で数学がどのように形式化できるか解説する教科書です．
* [The mechanics of proof](https://hrmacbeth.github.io/math2001/) 数学的な証明の書き方について，Lean を使って説明した教科書です．一部 Mathlib にないタクティクを使っているところがあるので，読まれる際は注意してください．
* [How to Prove It With Lean](https://djvelleman.github.io/HTPIwL/) 数学の証明の書き方を解説した教科書「How to Prove It」の内容を Lean を使って翻案したものです．
* [Lean4 タクティク逆引きリスト](https://lean-ja.github.io/tactic-cheatsheet/) Lean 4 の基本的なタクティク・コマンドの早見表です．

整数論については，次のようなものがあります.

* [A Computational Introduction to Number Theory and Algebra](https://shoup.net/ntb/) "Computational" とある通り，アルゴリズムの計算量の話題や暗号理論への応用などに詳しい本です．それだけでなく，解析的整数論の話題も含まれ，最低限の予備知識で最大限に整数論を楽しむことができます．
* [Elementary Number Theory: Primes, Congruences, and Secrets](https://wstein.org/ent/) 未読
* [Number Theory: In Context and Interactive](https://math.gordon.edu/ntic/) 未読
-/
