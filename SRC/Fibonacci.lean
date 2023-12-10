import Mathlib.Util.Time -- `#time` のために必要 --#
import Mathlib.Tactic --#
/-! # Fibonacci 数列

Lean で Fibonacci 数列は次のように定義できます．
-/

/-- フィボナッチ数列のナイーブな実装 -/
def fibonacci : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => fibonacci n + fibonacci (n + 1)

-- 実際にいくつかの値でテスト
#eval [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map fibonacci

/-! ## 線形時間の実装

上記の `fibonacci` 関数は定義通りの素直な実装ですが，かなり効率が悪いものです．実際に，計算の過程を追ってみるとそれがハッキリと分かります．`dbg_trace` で計算の過程を表示させてみましょう．
-/
namespace debug --#

def fibonacci : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  dbg_trace s!"fibonacci {n+2} を計算します."
  fibonacci n + fibonacci (n+1)

#eval fibonacci 5

end debug --#

/-! `dbg_trace` の出力を見ると，同じ数 `n` に対して何度も `fibonacci n` を計算していることが分かると思います．これは無駄の多い計算方法です．

以前の計算結果をなんらかの形で記憶することにより, 高速化できます．-/

/-- フィボナッチ数列の線形時間の実装 -/
def fib (n : ℕ) : ℕ :=
  (loop n).1
where
  -- ヘルパー関数を定義する
  loop : ℕ → ℕ × ℕ
    | 0 => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

#eval [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map fib

/-! ## 計算時間の比較
どの程度高速化できたのか，実際に実行時間を測定してみましょう．Mathlib にある `#time` コマンドで測定を行うことができます．実行するごとに測定値は異なるのですが，文字通り桁違いに高速化できていることが分かるはずです．
-/

#time #eval fibonacci 30

#time #eval fib 30

/-! ## 両者が等しいことの証明
Lean は定理証明支援系なので，2つの実装 `fibonacci` と `fib` が等しいことを証明することができます．

まずは，`fib` が `fibonacci` と同じ漸化式を満たすことを証明しましょう．
-/

-- n は自然数
variable (n : ℕ)

@[simp]
theorem fib_add : fib n + fib (n + 1) = fib (n + 2) := by rfl

/-! 定義から等しいことを Lean が自動的に推論してくれたので，`rfl` タクティクだけで証明ができました．`@[simp]` により，後で `simp` タクティクで利用できるように登録をしています．

漸化式が示せたら，後は帰納法で証明ができます．-/

/-- `fibonacci` と `fib` は同じ結果を返す -/
theorem fibonacci_eq_fib : fibonacci = fib := by
  -- 関数が等しいことを示すので，引数 `n` が与えられたとする
  ext n

  -- `n` についての強い帰納法で示す
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp_all [fibonacci]
