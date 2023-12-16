import Mathlib.Tactic --#

/-! # 選択ソート

選択ソートというのはソート(並び替え)アルゴリズムの一種で，「残りのうち最小の要素を先頭に」を繰り返すものです．

ここでは連結リスト `List` に対する実装例を紹介します．

また，並び替え対象のリスト `l : List α` に対しては，`α` が全順序集合という仮定をおきます．これは，`α` の要素を大小関係によって1列に並べることができることを意味します．これは少し強すぎる仮定ですが，簡単のためにこうしておきます．-/

open List --#

variable {α : Type*} [LinearOrder α]

/-! ## 停止証明なしの実装

選択ソートでは `l : List α` の最小値を取り出す操作が必要です．しかし空のリストに対して最小値は定義できないため，空リストの処理が問題になります．対処法としては

* 返り値の型を `Option α` にして，空リストの最小値は `none` とする
* 関数の定義域を「空でないリスト」に制限する
* 空リストに対してだけ，何か特別な値を返す

の少なくとも3通りの対処法が考えられます．
-/
namespace s1 --#

-- `Option` 型を返すバージョン
#guard minimum? [1, 4, 2, 10, 6] = some 1

#guard minimum? ([] : List ℕ) = none

-- 定義域を制限するバージョン
-- 配列が空でないことの証明を引数に要求する
theorem h : 0 < [1, 4, 2, 10, 6].length := by trivial

#guard minimum_of_length_pos h = 1

-- 空リストに対してだけ特別な値 `⊤` を返す
#guard minimum [1, 4, 2, 10, 6] = 1

#guard minimum ([] : List ℕ) = ⊤

end s1 --#
/-! ここでは3番目の方法を採用することにします．そうすると，選択ソートは次のように実装できます．-/
namespace s2 --#

partial def SelectionSort (l : List α) : List α :=
  let min := minimum? l
  match min with
  | none => []
  | some μ => μ :: SelectionSort (l.erase μ)

#guard SelectionSort [1, 4, 2, 10, 6] = [1, 2, 4, 6, 10]

end s2 --#
/-! ここで `def` の前についている `partial` というのは，停止することが保証されていない関数を実行するのに必要なキーワードです．`partial` を消すと，エラーになってしまいます．-/

/-! ## 停止証明付きの実装

停止証明を行うには，再帰のたびに「何か」が着実に減少すること，そして無限に減少し続けることはありえないことを証明する必要があります．

`termination_by` で再帰のたびに減少するはずの「何か」を指定することができ，`decreasing_by` でそれが実際に減少することの証明を提供することができます．`sorry` を使うと関数が停止することを Lean に信じさせることができます．
-/
namespace s3 --#

def SelectionSort (l : List α) : List α :=
  let min := minimum l
  match min with
  | ⊤ => []
  | some μ =>
    μ :: SelectionSort (l.erase μ)
  termination_by _ l => l.length
  decreasing_by
    simp_wf
    sorry

end s3 --#

/-! 実際に証明を埋めると，たとえば次のようになります．-/

namespace s4 --#

def SelectionSort (l : List α) : List α := by
  let min := minimum l
  match h : min with
  | ⊤ => exact []
  | some μ =>
    -- `μ` は `l` に属する
    have mem : μ ∈ l := by
      apply minimum_mem
      aesop

    -- `μ` を削除した残り
    let rest := l.erase μ

    -- `rest` の長さは `l` より小さい
    have : l.length > rest.length := calc
      l.length
      _ = rest.length + 1 := by rw [← length_erase_add_one mem]
      _ > rest.length := by simp_arith

    exact μ :: SelectionSort rest

  -- 再帰呼び出しのたびにリストの長さが短くなるので，有限回で停止
  termination_by _ l => l.length

end s4 --#
