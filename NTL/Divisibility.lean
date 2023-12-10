import Mathlib.Data.Int.Basic --#
import Mathlib.Algebra.Order.Group.Abs --#
import Mathlib.Algebra.Order.Ring.CharZero --#

namespace NTL --#

/-! # 整除関係

## 定義

まず言葉の定義から始めましょう．

整数 $a, b ∈ ℤ$ が与えられたとします．このとき $a$ が $b$ を{{i:割り切る}}とは，ある $z ∈ ℤ$ が存在して $a z = b$ となることを言います．これを {{i:$a ∣ b$ }}と書きます．
-/

/-! $a ∣ b$ であることを次のようにも言いますが，すべて同じ意味です．
* $b$ は $a$ で割り切れる
* $b$ は $a$ の{{i:倍数(multiple)}}である
* $a$ は $b$ の{{i:約数(divisor)}}である

$a ∣ b$ でないとき，斜線を入れて $a ∤ b$ と書きます．-/

/-! ## Lean での定義

Lean では，「割り切れる」ということは `Dvd` という型クラスで表現されます．その際，`∣` という記法も定義されています． -/

-- inductive Dvd.{u_1} : Type u_1 → Type u_1
-- number of parameters: 1
-- constructors:
-- Dvd.mk : {α : Type u_1} → (α → α → Prop) → Dvd α
#print Dvd

variable (α : Type) [self : Dvd α]

#check ((· ∣ ·) : α → α → Prop)

/-! そして整数 `Int` や自然数 `Nat` は `Dvd` のインスタンスです. -/

-- Int.instDvdInt
#synth Dvd Int

-- Nat.instDvdNat
#synth Dvd Nat

/-! ## 基本的な性質

以下で紹介する性質は `ℤ` だけでなく `ℕ` でも成り立ちますが，今回は代表して `ℤ` の話として説明します．

定義からすぐに従う基本的な性質として，まずどんな整数 $a ∈ℤ$ に対しても $1 ∣ a$ であり，かつ $a ∣ a$ です．
-/

/-- 1 はなんでも割り切る -/
theorem one_dvd (a : ℤ) : 1 ∣ a := by
  use a
  simp

/-- 必ず自分自身で割り切れる -/
theorem dvd_refl (a : ℤ) : a ∣ a := by
  use 1
  simp

/-! また，$a × 0 = 0$ なので任意の整数は $0$ を割り切ります．-/

theorem dvd_zero (a : ℤ) : a ∣ 0 := by
  use 0
  simp

/-! さらに，整数 $a, b, c ∈ ℤ$ について $a b ∣ c$ ならば $a ∣ c$ かつ $b ∣ c$ も成り立ちます． -/

theorem dvd_of_mul_right_dvd (a b c : ℤ) : a * b ∣ c → a ∣ c ∧ b ∣ c := by
  -- `a * b ∣ c` だと仮定します
  intro h

  -- 整除関係の定義から， `c = a * b * k` となる `k` が取れます．
  have ⟨k, hk⟩ := h
  clear h

  constructor
  case left =>
    -- したがって `a ∣ c` であることが従います．
    use b * k
    simp [hk, mul_assoc]

  case right =>
    -- 同様に `b ∣ c` であることも従います．
    use a * k
    simp [hk, ←mul_assoc]
    rw [show a * b = b * a from by simp [mul_comm]]

/-! ## 練習問題
次の `sorry` の部分を埋めてみてください．
-/

variable (a b c : ℤ)

-- 割り算の定義の確認
example : a ∣ b ↔ ∃ c : ℤ, b = a * c := by
  sorry

-- 倍数に何か乗じても倍数
example (h : a ∣ b) : a ∣ b * c := by
  sorry

example : ∃ a, 11 ∣ (2 ^ a + 1) := by
  sorry

end NTL --#
