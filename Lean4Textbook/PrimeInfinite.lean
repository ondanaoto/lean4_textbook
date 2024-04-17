import Mathlib.Tactic
import Mathlib.Data.Nat.Prime

/-- 自然数が0でも1でもなければ2以上 -/
lemma two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  -- 仮定から m = 0, 1 のときは考えなくていい
  repeat
    cases m; contradiction; rename_i m
  
  -- 自然数 0 ≤ m に対して 2 ≤ m + 2 を示せばよい
  simp_all; show 2 ≤ m + 2

  -- これは明らか
  simp_arith

/-- n が2以上なら， n を割り切る素数が存在する -/
lemma exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  -- n が素数かどうかで場合分けをする
  by_cases np : n.Prime

  -- n が素数のとき
  case pos =>
    -- 素数 p として n 自身を使えばいいので明らか
    use n, np

  -- n が素数ではないとき
  case neg =>
    -- n に関する完全帰納法で示す
    induction n using Nat.strong_induction_on with

    -- 帰納法の仮定を ih とする
    | h n ih =>
      -- n が素数でないということを， 素数の定義に従って書き直すと,
      rw [Nat.prime_def_lt] at np
      push_neg at np
      specialize np h

      -- n には自明でない約数 m が存在することがわかる．
      obtain ⟨m, mltn, mdvdn, mne1⟩ := np
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
