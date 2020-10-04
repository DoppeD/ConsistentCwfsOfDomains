module Nat.pred.AxiomProofs where

open import Nat.NbhSys.AxiomProofs
open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation
open import Nat.pred.Relation

pred↦-mono : ∀ {x y z} → x ⊑ₙ y → x pred↦ z →
            y pred↦ z
pred↦-mono x⊑z pred↦-intro₁ = pred↦-intro₁
pred↦-mono ⊑ₙ-intro₂ pred↦-intro₂ = pred↦-intro₂
pred↦-mono x⊑z (pred↦-intro₃ sz⊑x)
  = pred↦-intro₃ (⊑ₙ-trans sz⊑x x⊑z)

pred↦-↓closed : ∀ {x y z} → y ⊑ₙ z → x pred↦ z →
               x pred↦ y
pred↦-↓closed x⊑z (pred↦-intro₃ (⊑ₙ-intro₃ z⊑y))
  = pred↦-intro₃ (⊑ₙ-intro₃ (⊑ₙ-trans x⊑z z⊑y))
pred↦-↓closed ⊑ₙ-intro₁ pred↦-intro₁ = pred↦-intro₁
pred↦-↓closed ⊑ₙ-intro₁ pred↦-intro₂ = pred↦-intro₁
pred↦-↓closed ⊑ₙ-intro₂ pred↦-intro₂ = pred↦-intro₂

pred↦-↑directed : ∀ {x y z} → x pred↦ y → x pred↦ z →
                 ∀ conyz → x pred↦ (y ⊔ₙ z [ conyz ])
pred↦-↑directed _ predy↦z conₙ-bot₁ = predy↦z
pred↦-↑directed predx↦z _ conₙ-bot₂ = predx↦z
pred↦-↑directed predx↦z _ conₙ-0ₙ = predx↦z
pred↦-↑directed (pred↦-intro₃ (⊑ₙ-intro₃ sy⊑x))
  (pred↦-intro₃ (⊑ₙ-intro₃ sz⊑x)) (conₙ-sₙ conyz)
  = pred↦-intro₃ (⊑ₙ-intro₃ (⊑ₙ-⊔ sy⊑x sz⊑x conyz′))
  where conyz′ = conₙ-sₙ conyz

pred↦-con : ∀ {x y x′ y′} → x pred↦ y → x′ pred↦ y′ →
           Conₙ x x′ → Conₙ y y′
pred↦-con {y = ⊥ₙ} _ _ _ = conₙ-bot₁
pred↦-con {y′ = ⊥ₙ} _ _ _ = conₙ-bot₂
pred↦-con {y = 0ₙ} {y′ = 0ₙ} _ _ _ = conₙ-0ₙ
pred↦-con pred↦-intro₂ (pred↦-intro₃ ()) conₙ-bot₂
pred↦-con pred↦-intro₂ (pred↦-intro₃ ()) conₙ-0ₙ
pred↦-con (pred↦-intro₃ ()) pred↦-intro₂ conₙ-bot₁
pred↦-con (pred↦-intro₃ ()) pred↦-intro₂ conₙ-0ₙ
pred↦-con {sₙ (sₙ x)} {sₙ y} {sₙ x′} {y′} (pred↦-intro₃ (⊑ₙ-intro₃ (⊑ₙ-intro₃ y⊑x))) (pred↦-intro₃ (⊑ₙ-intro₃ y′⊑x′)) (conₙ-sₙ conxx′) = {!!}
