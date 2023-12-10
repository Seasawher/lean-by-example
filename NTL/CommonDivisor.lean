import Mathlib.Algebra.Order.Group.Abs --#
import Mathlib.Algebra.Order.Ring.CharZero --#
import Mathlib.Data.Nat.Basic --#
import Mathlib.Util.Time -- `#time` を使うため --#

namespace NTL --#

/-! # 公約数

この節では大小関係も考えるので，話を整数 $ℤ$ から自然数 $ℕ$ に限定します．

## 公約数と最大公約数

2 つの自然数 $a$ と $b$ に対して，そのどちらの約数でもあるような自然数のことを，{{i:公約数(common divisor)}}といいます．言い換えると，$d ∈ ℕ$ が $a$ と $b$ の公約数であるとは，$d ∣ a$ かつ $d ∣ b$ が成り立つことです．

[整除関係の節](./Divisibility.md)で見たように，$1$ はどんな自然数の約数でもあるため，$a$, $b$ の公約数は必ず1つは存在します．かつ，公約数が無限に存在することはありえません．したがって，最大のものが存在します．それを $a$ と $b$ の{{i:最大公約数(greatest common divisor)}}と呼ぶことにして，{{i:$\gcd(a, b)$}} と書きます．-/

/-! ## Lean での定義

有限集合から最大のものを取ってくるだけなので，じかに計算することができます．
-/

namespace Bad --#

def gcd (a b : ℕ) : ℕ := Id.run do
  -- `do` の代わりに `Id.run do` とすることで，
  -- pure code の中で do notation を使えます．
  -- 細かいことなので気にしなくていいです.

  -- `a` と `b` のうち小さい方までの自然数全体
  let xs := List.reverse $ List.range $ min a b

  for x in xs do
    if x ∣ a ∧ x ∣ b then
      return x

  -- このコードは実行されませんが必要です
  return 0


#guard gcd 12 18 = 6

#guard gcd 37 92 = 1

-- だいたい 2000 ~ 2200ms 程度
#time #eval gcd 12345678 87654321

end Bad --#

/-! 上記の `gcd` 関数で解決するように見えますが，そうではありません．$\min (a, b)$ に比例する計算時間が必要になるため，`#time` の出力を見ればわかるように少し桁が大きくなっただけでかなり計算に時間がかかるようになります．

また，これは後で分かることですが，公約数という概念が持つ構造を生かし切れていません．公約数を計算するもっと良い方法があります．-/

end NTL --#
