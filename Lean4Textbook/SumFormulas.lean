import Mathlib.Tactic.Ring

def linear_sum : Nat → Nat
| 0 => 0
| n + 1 => n + 1 + linear_sum n

#check linear_sum 4

theorem gauss : ∀ n : Nat, linear_sum n = n * (n + 1) / 2 := by
  intro n
  suffices 2 * linear_sum n = n * (n + 1) from by
    apply Eq.symm
    apply Nat.div_eq_of_eq_mul_right (by simp_arith)
    rw [this]
  apply Eq.symm
  induction n with
  | zero => rfl
  | succ h ih =>
    rw [linear_sum]
    calc
      (Nat.succ h) * (Nat.succ h + 1) = (h + 1) * (h + 2) := rfl
      _ = (2 + h) * (h + 1) := by rw [Nat.mul_comm, Nat.add_comm]
      _ = 2 * (h + 1) + h * (h + 1) := by rw [add_mul]
      _ = 2 * (h + 1) + 2 * linear_sum h := by rw [ih]
      _ = 2 * (h + 1 + linear_sum h) := by rw [← Nat.mul_add]
