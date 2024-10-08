-- lean by Example のaesopの例より引用
import Aesop
-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

/-- 関数の単射性 -/
def Function.Injective (f : X → Y) : Prop := ∀ ⦃a₁ a₂ : X⦄, f a₁ = f a₂ → a₁ = a₂

open Function

-- 合成 `g ∘ f` が単射なら、`f` も単射
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  show ∀ ⦃a₁ a₂ : X⦄, f a₁ = f a₂ → a₁ = a₂
  sorry
