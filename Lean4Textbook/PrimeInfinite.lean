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
    -- 素数 p として n 自身を使えばいいので明らか.
    use n, np

  -- n が素数ではないとき
  case neg =>
    -- n が素数でないということを， 素数の定義に従って書き直すと,
    rw [Nat.prime_def_lt] at np
    push_neg at np
    specialize np h

    -- n には自明でない約数 m が存在することがわかる．
    obtain ⟨m, _mltn, mdvdn, mne1⟩ := np

    -- ここで特に m は 0 ではない.
    have mne0 : m ≠ 0 := by
      -- 仮に m = 0 だとすると,
      intro (mz : m = 0)

      -- m ∣ n なので n = 0 となる.
      rw [mz, zero_dvd_iff] at mdvdn

      -- これは 2 ≤ n に矛盾する.
      simp_all

    -- m は 0 でも 1 でもないので， 先に示したことから 2 以上である．
    have mgt2 : 2 ≤ m := two_le mne0 mne1
    clear mne1 mne0 h -- もう使わない結果を消しておく

    -- 帰納法の仮定から m には素因数が存在するので，
    have ih := exists_prime_factor mgt2
    
    -- その素因数を p とする.
    obtain ⟨p, pp, pdvd⟩ := ih
    
    -- その素数 p が望みの性質を満たす．
    use p, pp
    trans m <;> assumption

/-- 素数は無限に存在する． 具体的には，任意の自然数 n に対して， 
n よりも大きな素数 p が存在する． -/
theorem primes_infinite : ∀ n, ∃ p, n < p ∧ Nat.Prime p := by
  -- 任意に自然数 n が与えられたとする
  intro n

  -- k = (n + 1)! + 1 とする．ただし ! は階乗を表す.
  set k := (n + 1).factorial + 1 with kh

  -- このとき k はもちろん 2 以上であるので，
  have ge2 : 2 ≤ k := calc
    2 ≤ n + 1 + 1 := by simp_arith 
    _ ≤ (n + 1).factorial + 1 := by gcongr; apply Nat.self_le_factorial
    _ = k := by rw [← kh]

  -- 先に示した定理により， k には素因数 p が存在する.
  obtain ⟨p, pp, pdvd⟩ := exists_prime_factor ge2

  -- この p が望みの性質を満たすことを示そう．
  refine ⟨p, ?_, pp⟩

  -- p > n を示せばよい.
  show p > n

  -- 仮に p ≤ n だったとする．
  by_contra! ple

  -- このとき p は (n + 1)! の約数になる.
  have : p ∣ (n + 1).factorial := by
    -- なぜなら， (n + 1)! = 1 × 2 × ... × (n + 1) の中に p が含まれるからだ．
    exact Nat.dvd_factorial pp.pos (show p ≤ n + 1 from by linarith)
  
  -- したがって p は 1 を割り切るということになる.
  replace : p ∣ 1 := by
    -- なぜなら， p は k の約数だったから (n + 1)! + 1 の約数でもあって
    rw [kh] at pdvd

    -- p の倍数同士の差をとっても p の倍数だからだ．
    convert Nat.dvd_sub' pdvd this
    simp

  -- これは p が素数であるという仮定に反しており，矛盾である．
  simp_all
