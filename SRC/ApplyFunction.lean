/-! # 関数の適用
Lean では関数 `f : A → B` を `x : A` に適用したいとき，括弧を省略して `f x` と書くことができます．
-/

abbrev ℕ := Nat

/-- 与えられた数を2倍する関数 -/
def double (x : ℕ) : ℕ := 2 * x

example : double 3 = 6 := rfl

/-! ## 関数の合成

複数の関数を一度に合成したいときには，合成するだけだと括弧が必要になります．-/

def triple (x : ℕ) : ℕ := 3 * x

example : triple (double (double 2)) = 24 := rfl

/-! `$` を使うことにより，括弧なしで引数を渡すことができます．`<|` と書いても同様です．-/

example : (triple $ double $ double 2) = 24 := by rfl

example : (triple <| double <| double 2) = 24 := by rfl

/-! また `∘` で関数を合成することができます．-/

example : (triple ∘ double ∘ double) 2 = 24 := by rfl

/-! ## 逆順の合成
時には，関数より先に引数を書きたいことがあります．その場合は `|>` が使えます．
-/

example : (2 |> double |> double |> triple) = 24 := by rfl

/-! ## 射影表記
`Foo.bar` という関数があり，その最初の非暗黙引数の型が `Foo` 型を持つとき, `x : Foo` に対して `Foo.bar x` と書く代わりに `x.bar` と書くことができます．
-/
universe u v

variable (α : Type u) (β : Type v)

/-- 平面 -/
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

/-- 原点 -/
def origin := Point.mk 0 0

-- フィールド `x` に対しては，
-- 自動的に `Point.x` という関数が生成されています
example : Point.x origin = 0 := rfl

-- `.x` を付けることで同じことができます
example : origin.x = 0 := rfl

/-! 上記の例では構造体のフィールドに対して射影表記でアクセスしていますが，フィールドでなくても使用できます．-/

def Point.sum (p : Point ℕ) : ℕ := p.x + p.y

example : Point.sum origin = 0 := rfl

example : origin.sum = 0 := rfl

/-! 名前空間 `Point` にない関数だと同様のことはできません． -/

def first (p : Point ℕ) : ℕ := p.x

#check_failure origin.first
