module Nat.pred.AxiomProofs where

open import Nat.NbhSys.AxiomProofs
open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation
open import Nat.pred.Relation

pred↦-mono : ∀ {x y z} → x ⊑ₙ y → x pred↦ z →
             y pred↦ z
pred↦-mono _ pred↦-intro₁
  = pred↦-intro₁
pred↦-mono x⊑y (pred↦-intro₂ sz⊑x)
  = pred↦-intro₂ (⊑ₙ-trans sz⊑x x⊑y)

pred↦-bottom : ∀ {x} → x pred↦ ⊥ₙ
pred↦-bottom = pred↦-intro₁

pred↦-↓closed : ∀ {x y z} → y ⊑ₙ z → x pred↦ z →
                x pred↦ y
pred↦-↓closed y⊑z (pred↦-intro₂ sz⊑x)
  = pred↦-intro₂ (⊑ₙ-trans (⊑ₙ-intro₃ y⊑z) sz⊑x)
pred↦-↓closed ⊑ₙ-intro₁ pred↦-intro₁
  = pred↦-intro₁

pred↦-↑directed : ∀ {x y z} → x pred↦ y → x pred↦ z →
                  ∀ conyz → x pred↦ (y ⊔ₙ z [ conyz ])
pred↦-↑directed pred↦-intro₁ predx↦y conₙ-bot₁
  = predx↦y
pred↦-↑directed pred↦-intro₁ predx↦y conₙ-bot₂
  = predx↦y
pred↦-↑directed (pred↦-intro₂ _) pred↦-intro₁ conₙ-bot₁
  = pred↦-intro₁
pred↦-↑directed (pred↦-intro₂ sy⊑x) pred↦-intro₁ conₙ-bot₂
  = pred↦-intro₂ sy⊑x
pred↦-↑directed (pred↦-intro₂ (⊑ₙ-intro₃ y⊑x))
  (pred↦-intro₂ (⊑ₙ-intro₃ z⊑x)) conyz
  = pred↦-intro₂ (⊑ₙ-intro₃ y⊔z⊑x)
  where y⊔z⊑x = ⊑ₙ-⊔ y⊑x z⊑x conyz

pred↦-con : ∀ {x y x′ y′} → x pred↦ y → x′ pred↦ y′ →
           Conₙ x x′ → Conₙ y y′
pred↦-con pred↦-intro₁ _ _ = conₙ-bot₁
pred↦-con (pred↦-intro₂ _) pred↦-intro₁ _ = conₙ-bot₂
pred↦-con (pred↦-intro₂ (⊑ₙ-intro₃ y⊑x)) (pred↦-intro₂ (⊑ₙ-intro₃ y′⊑x′)) consxsx′
  with (Conₙ-⊔ y⊑sx⊔sx′ y′⊑sx⊔sx′)
  where y⊑sx⊔sx′ = ⊑ₙ-trans (⊑ₙ-intro₃ y⊑x) (⊑ₙ-⊔-fst consxsx′)
        y′⊑sx⊔sx′ = ⊑ₙ-trans (⊑ₙ-intro₃ y′⊑x′) (⊑ₙ-⊔-snd consxsx′)
... | conₙ-sₙ conyy′ = conyy′
