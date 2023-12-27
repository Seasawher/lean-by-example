/-! # FizzBuzz
FizzBuzz プログラムは，与えられた自然数 `n` に対して，次のようなルールで文字を出力するものです．
1. 3 の倍数であれば `"Fizz"`
2. 5 の倍数であれば `"Buzz"`
3. ただし例外として 3 の倍数かつ 5 の倍数であれば `"FizzBuzz"`
4. それ以外の場合は，その数値を文字列に変換したもの
-/
def fizz_buzz (n : Nat) : String :=
  if n % 15 == 0 then
    "FizzBuzz"
  else if n % 3 == 0 then
    "Fizz"
  else if n % 5 == 0 then
    "Buzz"
  else
    toString n

#eval [1, 2, 3, 14, 15, 16, 20].map fizz_buzz
