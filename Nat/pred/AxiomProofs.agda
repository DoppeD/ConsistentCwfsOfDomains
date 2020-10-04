module Nat.pred.AxiomProofs where

open import Nat.NbhSys.AxiomProofs
open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation
open import Nat.pred.Relation

pred↦-mono : ∀ {x y z} → x ⊑ₙ y → x pred↦ z →
            y pred↦ z
pred↦-mono {y = ⊥ₙ} ⊑ₙ-intro₁ (pred↦-intro₁ ⊥⊑0 ⊑ₙ-intro₁)
  = pred↦-intro₁ ⊥⊑0 ⊑ₙ-intro₁
pred↦-mono {y = 0ₙ} ⊑ₙ-intro₁ (pred↦-intro₁ _ ⊑ₙ-intro₁)
  = pred↦-intro₁ ⊑ₙ-intro₂ ⊑ₙ-intro₁
pred↦-mono {y = 0ₙ} ⊑ₙ-intro₂ predx↦z
  = predx↦z
pred↦-mono {y = sₙ y} ⊑ₙ-intro₁ (pred↦-intro₁ _ ⊑ₙ-intro₁)
  = pred↦-intro₂ s⊥⊑sy s⊥⊑sy
  where s⊥⊑sy = ⊑ₙ-intro₃ ⊑ₙ-intro₁
pred↦-mono {y = sₙ y} (⊑ₙ-intro₃ x⊑y) (pred↦-intro₂ (⊑ₙ-intro₃ _)
  (⊑ₙ-intro₃ z⊑x))
  = pred↦-intro₂ (⊑ₙ-intro₃ ⊑ₙ-intro₁) (⊑ₙ-intro₃ z⊑y)
  where z⊑y = ⊑ₙ-trans z⊑x x⊑y

pred↦-bottom : ∀ {x} → x pred↦ ⊥ₙ
pred↦-bottom {⊥ₙ} = pred↦-intro₁ ⊑ₙ-intro₁ ⊑ₙ-intro₁
pred↦-bottom {0ₙ} = pred↦-intro₁ ⊑ₙ-intro₂ ⊑ₙ-intro₁
pred↦-bottom {sₙ _}
  = pred↦-intro₂ (⊑ₙ-intro₃ ⊑ₙ-intro₁) (⊑ₙ-intro₃ ⊑ₙ-intro₁)

pred↦-↓closed : ∀ {x y z} → y ⊑ₙ z → x pred↦ z →
               x pred↦ y
pred↦-↓closed {⊥ₙ} ⊑ₙ-intro₁ (pred↦-intro₁ _ ⊑ₙ-intro₁)
  = pred↦-bottom
pred↦-↓closed {0ₙ} y⊑z (pred↦-intro₁ _ z⊑x)
  = pred↦-intro₁ ⊑ₙ-intro₂ y⊑0
  where y⊑0 = ⊑ₙ-trans y⊑z z⊑x
pred↦-↓closed {sₙ x} y⊑z (pred↦-intro₂ (⊑ₙ-intro₃ _) (⊑ₙ-intro₃ z⊑x))
  = pred↦-intro₂ (⊑ₙ-intro₃ ⊑ₙ-intro₁) (⊑ₙ-intro₃ y⊑x)
  where y⊑x = ⊑ₙ-trans y⊑z z⊑x

pred↦-↑directed : ∀ {x y z} → x pred↦ y → x pred↦ z →
                 ∀ conyz → x pred↦ (y ⊔ₙ z [ conyz ])
pred↦-↑directed {⊥ₙ} (pred↦-intro₁ _ ⊑ₙ-intro₁)
  (pred↦-intro₁ _ ⊑ₙ-intro₁) conₙ-bot₁
  = pred↦-bottom
pred↦-↑directed {⊥ₙ} (pred↦-intro₁ _ ⊑ₙ-intro₁)
  (pred↦-intro₁ _ ⊑ₙ-intro₁) conₙ-bot₂
  = pred↦-bottom
pred↦-↑directed {0ₙ} _ (pred↦-intro₁ _ ⊑ₙ-intro₁)
  conₙ-bot₁
  = pred↦-bottom
pred↦-↑directed {0ₙ} predx↦y (pred↦-intro₁ _ ⊑ₙ-intro₁)
  conₙ-bot₂
  = predx↦y
pred↦-↑directed {0ₙ} _ (pred↦-intro₁ _ ⊑ₙ-intro₂)
  conₙ-bot₁
  = pred↦-intro₁ ⊑ₙ-intro₂ ⊑ₙ-intro₂
pred↦-↑directed {0ₙ} _ (pred↦-intro₁ _ ⊑ₙ-intro₂) conₙ-0ₙ
  = pred↦-intro₁ ⊑ₙ-intro₂ ⊑ₙ-intro₂
pred↦-↑directed {sₙ x} (pred↦-intro₂ _ (⊑ₙ-intro₃ y⊑x))
  (pred↦-intro₂ _ (⊑ₙ-intro₃ z⊑x)) conyz
  = pred↦-intro₂ (⊑ₙ-intro₃ ⊑ₙ-intro₁) (⊑ₙ-intro₃ y⊔z⊑x)
  where y⊔z⊑x = ⊑ₙ-⊔ y⊑x z⊑x conyz

pred↦-con : ∀ {x y x′ y′} → x pred↦ y → x′ pred↦ y′ →
           Conₙ x x′ → Conₙ y y′
pred↦-con (pred↦-intro₁ _ ⊑ₙ-intro₁) _ conₙ-bot₁
  = conₙ-bot₁
pred↦-con _ (pred↦-intro₁ _ ⊑ₙ-intro₁) conₙ-bot₂
  = conₙ-bot₂
pred↦-con (pred↦-intro₁ _ _) (pred↦-intro₁ _ ⊑ₙ-intro₁) conₙ-0ₙ
  = conₙ-bot₂
pred↦-con (pred↦-intro₁ _ ⊑ₙ-intro₁)
  (pred↦-intro₁ _ ⊑ₙ-intro₂) conₙ-0ₙ
  = conₙ-bot₁
pred↦-con (pred↦-intro₁ _ ⊑ₙ-intro₂)
  (pred↦-intro₁ _ ⊑ₙ-intro₂) conₙ-0ₙ
  = conₙ-0ₙ
pred↦-con (pred↦-intro₂ _ (⊑ₙ-intro₃ y⊑x))
  (pred↦-intro₂ _ (⊑ₙ-intro₃ y′⊑x′)) (conₙ-sₙ conxx′)
  = Conₙ-⊔ y⊑x⊔x′ y′⊑x⊔x′
  where y⊑x⊔x′ = ⊑ₙ-trans y⊑x (⊑ₙ-⊔-fst conxx′)
        y′⊑x⊔x′ = ⊑ₙ-trans y′⊑x′ (⊑ₙ-⊔-snd conxx′)
