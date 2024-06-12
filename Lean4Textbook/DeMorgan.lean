-- ドモルガンの法則の中に一つだけ、証明に排中律が必要な命題がある。
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


-- では、自力でドモルガンの法則を示してみます！
-- 実況の時は、各証明の行ごとにコメントを書いていこうと思います。
section MyDeMorgan

variable (p q : Prop)

theorem nor : ¬(p ∨ q) → (¬p) ∧ (¬q) := by
  intro h
  constructor
  . intro hp
    apply h
    left
    exact hp
  . intro hq
    apply h
    right
    exact hq

theorem notandnot : (¬p) ∧ (¬q) → ¬(p ∨ q) := by
  intro h porq
  rcases porq with hp | hq
  . apply h.left
    exact hp
  . apply h.right
    exact hq

theorem notornot : (¬p) ∨ (¬q) → ¬(p ∧ q) := by
  intro h pandq
  rcases h with notp | notq
  . apply notp
    exact pandq.left
  . apply notq
    exact pandq.right

theorem nand : ¬(p ∧ q) → (¬p) ∨ (¬q) := by
  intro nand
  have : p ∨ ¬p := by exact Classical.em p
  rcases this with hp | notp
  . apply Or.inr
    intro hq
    apply nand
    exact And.intro hp hq
  . exact Or.inl notp

end MyDeMorgan
