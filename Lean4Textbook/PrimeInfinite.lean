import Mathlib.Tactic
import Mathlib.Data.Nat.Prime

/-- 自然数が0でも1でもなければ2以上 -/
lemma two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  -- 仮定から m = 0 のときは考えなくていい
  cases m; contradiction; rename_i n
  
  -- 仮定から m = 1 のときも考えなくていい
  cases n; contradiction; rename_i k
  
  -- 自然数 0 ≤ k に対して 2 ≤ k + 2 を示せばよい
  simp_all; show 2 ≤ k + 2

  -- これは明らか
  simp_arith

lemma exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  . rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p, n < p ∧ Nat.Prime p := by
  intro n

  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    have : 1 ≤ Nat.factorial (n + 1) := calc
      1 ≤ n + 1 := by linarith
      _ ≤ Nat.factorial (n + 1) := by apply Nat.self_le_factorial
    linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine' ⟨p, _, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
    apply Nat.dvd_factorial (pp.pos) (by linarith)
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
  aesop
