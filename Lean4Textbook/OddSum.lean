import Mathlib.Tactic
/--
小さい順にn個の奇数の和を計算する関数．
odd_sum 0 = 0
odd_sum 1 = 1
odd_sum 2 = 1 + 3 = 4
odd_sum 3 = 1 + 3 + 5 = 9
odd_sum 4 = 1 + 3 + 5 + 7 = 16
-/
def odd_sum : Nat → Nat
| 0 => 0
| n + 1 => 2 * n + 1 + odd_sum n

#eval odd_sum 4

theorem odd_sum_eq : ∀ n : Nat, odd_sum n = n * n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    have : Nat.succ k = k + 1 := by rfl
    rw [this]
    rw [odd_sum]
    rw [ih]
    ring
