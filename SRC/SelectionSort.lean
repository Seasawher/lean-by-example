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

-- `Option` 型を返すバージョン
#guard minimum? [1, 4, 2, 10, 6] = some 1

#guard minimum? ([] : List ℕ) = none

-- 定義域を制限するバージョン
-- 配列が空でないことの証明を引数に要求する
#guard minimum_of_length_pos (show 0 < [1, 4, 2, 10, 6].length from by trivial) = 1

-- 空リストに対してだけ特別な値 `⊤` を返す
#guard minimum [1, 4, 2, 10, 6] = 1

#guard minimum ([] : List ℕ) = ⊤

/-! ここでは2番目の方法を採用することにします．そうすると，選択ソートは次のように実装できます．-/
namespace Partial --#

partial def selection_sort (l : List α) : List α :=
  if hl : 0 < l.length then
    -- 最小値を選択する
    let μ : α := minimum_of_length_pos hl

    -- リストから取り除く
    let rest := l.erase μ

    -- 最小値を先頭にする
    -- これを再帰的に繰り返す
    μ :: (selection_sort rest)
  else
    []

#guard selection_sort [1, 4, 2, 10, 6] = [1, 2, 4, 6, 10]

end Partial --#
/-! ここで `def` の前についている `partial` というのは，停止することが保証されていない関数を実行するのに必要なキーワードです．`partial` を消すと，エラーになってしまいます．-/

/-! ## 停止証明付きの実装

停止証明を行うには，再帰のたびに「何か」が着実に減少すること，そして無限に減少し続けることはありえないことを証明する必要があります．

`termination_by` で再帰のたびに減少するはずの「何か」を指定することができ，`decreasing_by` でそれが実際に減少することの証明を提供することができます．

ここでは `termination_by` だけで停止性を証明することができます．例えば，次のようにします:
-/

/-- 選択ソート -/
def selection_sort (l : List α) : List α :=
  if hl : 0 < l.length then
    let μ : α := minimum_of_length_pos hl

    -- `μ` はリストの要素
    have mem : μ ∈ l := by
      apply minimum_mem
      simp [coe_minimum_of_length_pos]

    let rest := l.erase μ

    -- 停止性を示すための補題
    have : l.length > rest.length := calc
      l.length
      _ = rest.length + 1 := by rw [← length_erase_add_one mem]
      _ > rest.length := by simp_arith

    μ :: (selection_sort rest)
  else
    []
  -- 再帰呼び出しのたびにリストの長さが短くなるので，有限回で停止する
  termination_by _ l => l.length

/-! ## ソートであることの証明
`selection_sort` がソートであることを証明します． ソートであるということを示すには，リスト `l : List α` に対して

1. `selection_sort l` が `l` の置換（要素を並び替えたもの）であること
2. `selection_sort l` の要素が大小関係の順に並んでいること

の2つを示せば十分です．

### 置換であること
リスト `l1` が `l2` の置換であることは `l1 ~ l2` と書くことができます．
-/

/-- 選択ソートが返すリストは，元のリストと要素の順番だけしか異ならない -/
theorem perm_selection_sort (l : List α) : l ~ selection_sort l := by
  -- リスト `l` の長さに対する帰納法を使う
  induction' ih : l.length generalizing l

  -- `selection_sort` を展開する
  all_goals
    unfold selection_sort
    simp_all [ih]

  -- リストの長さが 0 のとき
  case zero => exact length_eq_zero.mp ih

  -- リストの長さが `n + 1` であるとき
  case succ n IH =>
    -- ゴールが複雑で見づらいので変数を導入する
    set μ := minimum_of_length_pos (_ : 0 < length l)
    set rest := l.erase μ

    -- `μ` が `l` の要素であることを再度示す
    have mem : μ ∈ l := by
      apply minimum_mem
      simp [coe_minimum_of_length_pos]

    -- `rest` の長さについての補題を再度示す
    have rlen : rest.length = n := by
      convert List.length_erase_of_mem mem
      simp [ih]

    -- 帰納法の仮定により，`selection_sort rest ~ rest` が言える
    have hr : selection_sort rest ~ rest := Perm.symm (IH rest rlen)

    -- 置換の推移性により，`l ~ μ :: rest` を示せばいい
    suffices l ~ μ :: rest from by
      apply this.trans
      simp [hr.symm]

    -- `List.erase` の性質から示せる
    exact perm_cons_erase mem

/-! ### 要素を整列させること
次に，`selection_sort l` の要素が大小関係の順に並んでいること，つまりソート済みであることを示します．
-/

/-- selection sort が返すリストは，並び替え済み -/
theorem sorted_selection_sort (l : List α) : Sorted (· ≤ ·) $ selection_sort l := by
  -- リスト `l` の長さに対する帰納法を使う
  induction' ih : l.length generalizing l

  -- `selection_sort` を展開する
  all_goals
    unfold selection_sort
    simp_all [ih]

  case succ n IH =>
    -- ゴールが複雑で見づらいので変数を導入する
    set μ := minimum_of_length_pos (_ : 0 < length l)
    set rest := l.erase μ

    -- `rest` は `l` の部分集合
    have rsub : rest ⊆ l := erase_subset μ l

    -- `selection_sort` が置換を返すことを利用する
    have rperm : selection_sort rest ~ rest := by
      exact Perm.symm (perm_selection_sort rest)

    -- `selection_sort rest` は `l` の部分集合
    have subh : selection_sort rest ⊆ l := by
      exact (Perm.subset_congr_left (id (Perm.symm rperm))).mp rsub

    constructor
    case left =>
      -- 最小値は残りの部分のどの要素よりも小さいことを示す
      show ∀ (b : α), b ∈ selection_sort rest → minimum l ≤ ↑b
      intro b hb
      exact minimum_le_of_mem' (subh hb)
    case right =>
      -- 残りの部分がソート済みであることを示す
      show Sorted (· ≤ ·) (selection_sort rest)
      apply IH rest

      -- `μ` が `l` の要素であることを再度示す(3回目)
      have mem : μ ∈ l := by
        apply minimum_mem
        simp [coe_minimum_of_length_pos]

      -- あとは `rest` の長さが `n` であることを示すだけ
      convert List.length_erase_of_mem mem
      simp [ih]
