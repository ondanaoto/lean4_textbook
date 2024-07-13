import Mathlib.Data.Real.Basic
/-
# 概要
rewrite タクティク`rw`の紹介
詳細は[Lean by Example](https://lean-ja.github.io/lean-by-example/Tactic/Rw.html)
の`rw`のsectionをご覧ください(**日本語の記事！**)。
`rw`を使った例は[Mathematics in Leanのライブコーディングのアーカイブ](https://youtube.com/live/NQEV0HDAjFA?feature=share)
にたくさん登場するのでぜひみてね〜！
-/

example (a b c : Nat) (hab: a = b) (hbc: b = c) : a = c := by
  -- `hab`という仮定を使って結論である`a=c`を書き換える
  -- `hab`より`a=b`なので、`a=c`の`a`を`b`に書き換える
  rw [hab]
  -- `b=c`を示す問題に変化した。
  -- なら、仮定`hbc`があるのでそれを引っ張ってくればいい！
  exact hbc

-- mathlibには実装済みの等式があるので、それらを`rw`で利用することもできます！
#check (mul_comm)
#check (mul_assoc)

variable (x y z: ℝ)
-- `∀`の部分を変数とみなし、代入することで等式を得ることができる
#check (mul_comm x y)
#check (mul_assoc x y z)

example (a b c : ℝ) : (c * b) * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc]
  rw [mul_comm c a]

-- 引数を与えない場合は、最初に適用可能な部分に一度だけ適用するようになる。
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

-- `←`を用いると、等式の右辺を左辺に書き換えることもできる。
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f)
  : a * (b * e) = c * (d * f) := by
  rw [← mul_assoc]
  rw [h]
  rw [h']
  rw [mul_assoc]
