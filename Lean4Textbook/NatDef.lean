inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def zero := MyNat.zero

def one := MyNat.succ MyNat.zero

def two := MyNat.succ (MyNat.succ MyNat.zero)

def MyNat.add : MyNat → MyNat → MyNat
  | .zero, k => k
  | .succ n, k => .succ (MyNat.add n k)

instance : Add MyNat where
  add := MyNat.add

example : one + one = two := by calc
  one + one = MyNat.add one one := by rfl
          _ = MyNat.add (MyNat.succ MyNat.zero) one := rfl
          _ = MyNat.succ (MyNat.add MyNat.zero one) := rfl
          _ = MyNat.succ one := rfl
          _ = MyNat.succ (MyNat.succ MyNat.zero) := rfl
          _ = two := rfl
