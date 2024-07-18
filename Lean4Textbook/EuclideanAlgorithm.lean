def euclid (n m : Nat) : Nat :=
  match n, m with
  | 0, m => m
  | n, 0 => n
  | .succ k, .succ l =>
    let n := .succ k
    let m := .succ l
    have hn : n > 0 := Nat.zero_lt_succ k
    have hm : m > 0 := Nat.zero_lt_succ l
    if n = m then
      n
    else if n < m then
      have : m - n < m := Nat.sub_lt hm hn
      euclid n (m - n)
    else
      have : n - m < n := Nat.sub_lt hn hm
      euclid (n - m) m

theorem gcd_euclid (n m : Nat) : Nat.gcd n m = euclid n m :=
  match n, m with
  | 0, m => by simp [Nat.gcd_zero_left, euclid]
  | n, 0 => by
    simp [Nat.gcd_zero_right]
    match n with
    | 0 => simp [euclid]
    | _ + 1 => simp [euclid]
  | .succ k, .succ l => by
    if h : k = l then
      simp [h, euclid]
    else
      let m : Nat := .succ k
      let n : Nat := .succ l
      have hmk : m = Nat.succ k := rfl
      have hnl : n = Nat.succ l := rfl
      have mpos : m > 0 := Nat.zero_lt_succ k
      have npos : n > 0 := Nat.zero_lt_succ l
      rw [← hmk, ← hnl]
      have hmn : m < n ∨ n < m := by
        have :m ≠ n := by
          rw[hnl, hmk]
          intro skl
          apply h
          exact Nat.succ.inj skl
        have : m ≤ n ∨ n ≤ m := Nat.le_total m n
        rcases this with hle | hle
        . left; exact Nat.lt_of_le_of_ne hle this
        . right; exact Nat.lt_of_le_of_ne hle (this.symm)

      rcases hmn with hmn | hmn
      . simp [hmn, euclid, h, ← hmk]
        rw [show l - k = n - m from by simp [hmk, hnl]]
        sorry
      . simp [hmn, euclid, h, ←hmk, ← hnl]
        simp [show ¬ m < n from Nat.not_lt_of_gt hmn]
        rw [show k - l = m - n from by simp [hmk, hnl]]
        sorry
