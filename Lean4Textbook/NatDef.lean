#check Nat

example : 1 + 1 = 2 := rfl

inductive Nat' where
-- 0は自然数とする
| zero : Nat'
-- nが自然数ならsucc nも自然数とする
| succ (n : Nat') : Nat'

-- 1は0の後者として定義する
def one := Nat'.succ Nat'.zero

-- 2は1の後者として定義する
def two := Nat'.succ one

-- 0はどの自然数の後者にもならない
theorem succ_ne_zero
(n : Nat')
: Nat'.succ n ≠ Nat'.zero
:= Nat'.noConfusion

-- 後者関数は単射である
theorem succ_inj
(n m : Nat')
(h : Nat'.succ n = Nat'.succ m)
: n = m
:= by exact Nat'.succ.inj h

-- 数学的帰納法
theorem ind
(E : Nat' → Prop)
(h0 : E Nat'.zero)
(hk : ∀ k : Nat', E k → E (Nat'.succ k))
(n : Nat')
: E n
:= by
induction n with
| zero => exact h0
| succ n hn => exact hk n hn

-- Leanでは足し算をどうやって定義してるっけ
#check Nat.add

-- Nat'に足し算を定義する
def Nat'.add : Nat' → Nat' → Nat'
| n, .zero => n
| n, .succ m => .succ (Nat'.add n m)

-- +を使ったらNat'.addを意味していることをLeanに教える
instance : Add Nat' where add := Nat'.add

theorem one_add_one_eq_two : one + one = two := by
calc
  one + one = Nat'.add one one := by rfl -- 足し算の定義を展開
  _ = Nat'.add one (Nat'.succ Nat'.zero) := by rfl -- 第二引数のoneを展開
  _ = Nat'.succ (Nat'.add one Nat'.zero) := by rfl -- 足し算の定義の2つ目のケース
  _ = Nat'.succ one := by rfl -- ()の中身を、足し算の定義の1つ目のケースに基づいて計算。
  _ = two := by rfl -- twoとはoneの後者として定義していた
