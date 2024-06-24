-- ド・モルガンの法則の中に一つだけ、直観主義論理の範囲で示せない命題がある。
-- 何でしょうか？

import Mathlib.Logic.Basic

-- `¬(p ∨ q) ↔ ¬p ∧ ¬q`の実装
#check Decidable.not_or_iff_and_not

-- `¬(a ∧ b) ↔ ¬a ∨ ¬b`の実装
#check not_and_or

-- 排中律`p ∨ ¬p`の実装
#check Classical.em



-- leanでは排中律は公理ではなく他の公理から導出されている
#print axioms Classical.em

-- `¬(p ∨ q) ↔ ¬p ∧ ¬q`の証明には特にaxiomは使ってないようだ(leanがデフォルトで採用している公理はのぞいて)
#print axioms Decidable.not_or_iff_and_not

-- `¬(a ∧ b) ↔ ¬a ∨ ¬b`の証明では排中律が引用している公理を利用している
#print axioms not_and_or


-- では、自力でド・モルガンの法則を示してみます！
section MyDeMorgan

variable (p q : Prop)

theorem nor : ¬(p ∨ q) → (¬p) ∧ (¬q) := by
  intro norpq
  -- ¬p と¬q をそれぞれ示せばいい
  constructor
  . intro hp
    apply norpq
    left
    exact hp
  . intro hq
    apply norpq
    right
    exact hq

theorem nor_reverse : (¬p) ∧ (¬q) → ¬(p ∨ q) := by
  intro notpnotq porq
  -- ¬pと¬qを導き、仮定を追加
  obtain ⟨notp, notq⟩ := notpnotq
  -- pの場合とqの場合で場合わけ
  rcases porq with hp | hq
  . apply notp
    exact hp
    -- notqという関数にhqを代入することでFalse型のtermを構成することができる
  . exact (notq hq)

#print axioms nor_reverse

theorem nand_reverse : (¬p) ∨ (¬q) → ¬(p ∧ q) := by
  intro notp_or_notq pandq
  rcases notp_or_notq with notp | notq
  . exact notp (pandq.left)
  . exact notq (pandq.right)

theorem nand : ¬(p ∧ q) → (¬p) ∨ (¬q) := by
  intro nandpq
  -- 排中律を使ってp ∨ ¬pを用意する
  have p_or_notp : p ∨ ¬p := Classical.em p
  rcases p_or_notp with hp | notp
  . right
    intro hq
    apply nandpq
    exact ⟨hp, hq⟩
  . left;
    -- 仮定の中に示したい命題と同じものがあるときは
    -- assumptionで証明が完了する
    assumption

#print axioms nand

end MyDeMorgan

-- ド・モルガンの法則と弱い排中律が同値であることを示します
-- 参考文献: https://ncatlab.org/nlab/show/weak+excluded+middle

def de_morgan := ∀ (p q : Prop), ¬(p ∧ q) → (¬p) ∨ (¬q)

def weak_em := ∀ (p : Prop), ¬ p ∨ ¬ ¬ p

theorem de_morgan_iff_weak_em : de_morgan ↔ weak_em := by
  constructor

  . rw[de_morgan]
    intro de_morgan p
    have nand_p_notp : ¬(p ∧ ¬p) := by
      intro p_and_notp
      obtain ⟨hp, notp⟩ := p_and_notp
      exact notp hp
    apply de_morgan p ¬p
    exact nand_p_notp
  . intro weakem
    rw [de_morgan]
    intro p q nandpq
    have weak_p := weakem p
    rcases weak_p with notp | nnp
    . left; assumption
    . right
      intro hq
      have notp : ¬p := by
        intro hp
        apply nandpq
        exact ⟨hp, hq⟩
      exact nnp notp

#print axioms de_morgan_iff_weak_em
