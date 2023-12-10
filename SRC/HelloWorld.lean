/-! # Hello World

`Hello World` という文字列を出力するプログラムです．

`#eval` だけで次のように書くことができます.
-/

#eval "Hello World"

/-! `IO.println` を用いて次のようにしても，同じようなことができます．-/

def main : IO Unit :=
  IO.println "Hello World"

#eval main
