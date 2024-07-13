import Mathlib.Tactic.Ring

def lin_sum' (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n + 1 + lin_sum' n

def lin_sum : Nat → Nat
| 0 => 0
| n + 1 => n + 1 + lin_sum n

#eval lin_sum 3
#eval lin_sum 4
#eval lin_sum 5
#eval lin_sum 6

theorem hoge (n : Nat) : 2 * lin_sum n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    calc
      _ = 2 * ((n + 1) + lin_sum n)
        := rfl
      _ = 2 * (n + 1) + 2 * lin_sum n
        := Nat.mul_add 2 (n + 1) (lin_sum n)
      _ = 2 * (n + 1) + n * (n + 1) := congrArg (HAdd.hAdd (2 * (n + 1))) hn
      _ = (2 + n) * (n + 1) := (Nat.add_mul 2 n (n + 1)).symm
      _ = (n + 1) * (n + 2) := by ring
      _ = (Nat.succ n) * (Nat.succ n + 1) := rfl
  done

example (x : Nat): (x + 1)^2 = x^2 + 2*x + 1 := by ring
