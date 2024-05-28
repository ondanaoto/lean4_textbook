inductive MyNat : Type where
  -- ゼロは自然数である
  | zero : MyNat
  -- 自然数の次の数は自然数である
  | succ : MyNat → MyNat

def zero := MyNat.zero

-- 1は0の次の数と定義する
def one := MyNat.succ MyNat.zero

-- 2は1の次の数と定義する
def two := MyNat.succ (MyNat.succ MyNat.zero)

-- 自然数の足し算の定義
def MyNat.add : MyNat → MyNat → MyNat
  -- 第1項が0なら第2項が足し算の結果ですよ
  | .zero, k => k
  -- (nの次の数)とkの足し算は(nとkの足し算)の次の数としましょう
  | .succ n, k => .succ (MyNat.add n k)

-- + と書いたら上で定義した足し算のことになりますよという呪文
instance : Add MyNat where
  add := MyNat.add

example : one + one = two := by calc
  one + one = MyNat.add one one := by rfl -- + を展開した
          _ = MyNat.add (MyNat.succ MyNat.zero) one := rfl -- 第1項のoneを展開した
          _ = MyNat.succ (MyNat.add MyNat.zero one) := rfl -- 足し算の定義に従って式変形した
          _ = MyNat.succ one := rfl -- 足し算は第1項が0なら第2項が足し算の結果になるのだった
          _ = MyNat.succ (MyNat.succ MyNat.zero) := rfl -- oneを展開した
          _ = two := rfl -- twoはそういえば0の次の次だったね!
