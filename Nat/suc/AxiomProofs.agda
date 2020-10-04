module Nat.suc.AxiomProofs where

open import Nat.NbhSys.AxiomProofs
open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation
open import Nat.suc.Relation

suc↦-mono : ∀ {x y z} → x ⊑ₙ y → x suc↦ z →
            y suc↦ z
suc↦-mono ⊑ₙ-intro₁ (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ (⊑ₙ-trans z⊑sx (⊑ₙ-intro₃ ⊑ₙ-intro₁))
suc↦-mono ⊑ₙ-intro₂ (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ z⊑sx
suc↦-mono (⊑ₙ-intro₃ x⊑y) (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ (⊑ₙ-trans z⊑sx (⊑ₙ-intro₃ (⊑ₙ-intro₃ x⊑y)))

suc↦-↓closed : ∀ {x y z} → y ⊑ₙ z → x suc↦ z →
               x suc↦ y
suc↦-↓closed ⊑ₙ-intro₁ (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ ⊑ₙ-intro₁
suc↦-↓closed (⊑ₙ-intro₃ y⊑z) (suc↦-intro₁ (⊑ₙ-intro₃ z⊑ssx))
  = suc↦-intro₁ (⊑ₙ-intro₃ (⊑ₙ-trans y⊑z z⊑ssx))

suc↦-↑directed : ∀ {x y z} → x suc↦ y → x suc↦ z →
                 ∀ conyz → x suc↦ (y ⊔ₙ z [ conyz ])
suc↦-↑directed _ (suc↦-intro₁ z⊑sx) conₙ-bot₁
  = suc↦-intro₁ z⊑sx
suc↦-↑directed (suc↦-intro₁ y⊑sx) (suc↦-intro₁ _) conₙ-bot₂
  = suc↦-intro₁ y⊑sx
suc↦-↑directed (suc↦-intro₁ ()) (suc↦-intro₁ z⊑sx) conₙ-0ₙ
suc↦-↑directed (suc↦-intro₁ (⊑ₙ-intro₃ y⊑x))
  (suc↦-intro₁ (⊑ₙ-intro₃ z⊑x)) (conₙ-sₙ conyz)
  = suc↦-intro₁ (⊑ₙ-intro₃ (⊑ₙ-⊔ y⊑x z⊑x conyz))

suc↦-con' : ∀ {x x′} → x ⊑ₙ 0ₙ → x′ ⊑ₙ 0ₙ → Conₙ x x′
suc↦-con' ⊑ₙ-intro₁ ⊑ₙ-intro₁ = conₙ-bot₁
suc↦-con' ⊑ₙ-intro₁ ⊑ₙ-intro₂ = conₙ-bot₁
suc↦-con' ⊑ₙ-intro₂ ⊑ₙ-intro₁ = conₙ-bot₂
suc↦-con' ⊑ₙ-intro₂ ⊑ₙ-intro₂ = conₙ-0ₙ

suc↦-con : ∀ {x y x′ y′} → x suc↦ y → x′ suc↦ y′ →
           Conₙ x x′ → Conₙ y y′
suc↦-con {y = ⊥ₙ} _ _ _ = conₙ-bot₁
suc↦-con {y = sₙ y} {y′ = ⊥ₙ} _ _ _ = conₙ-bot₂
suc↦-con {y′ = 0ₙ} _ (suc↦-intro₁ ()) _
suc↦-con {y = 0ₙ} (suc↦-intro₁ ()) _ _
suc↦-con (suc↦-intro₁ (⊑ₙ-intro₃ ⊑ₙ-intro₁))
  (suc↦-intro₁ (⊑ₙ-intro₃ y′⊑sx′)) conₙ-bot₁
  = conₙ-sₙ conₙ-bot₁
suc↦-con (suc↦-intro₁ (⊑ₙ-intro₃ y⊑sx))
  (suc↦-intro₁ (⊑ₙ-intro₃ ⊑ₙ-intro₁)) conₙ-bot₂
  = conₙ-sₙ conₙ-bot₂
suc↦-con (suc↦-intro₁ (⊑ₙ-intro₃ y⊑sx))
  (suc↦-intro₁ (⊑ₙ-intro₃ y′⊑sx′)) conₙ-0ₙ
  = conₙ-sₙ (suc↦-con' y⊑sx y′⊑sx′)
suc↦-con (suc↦-intro₁ (⊑ₙ-intro₃ y⊑sx))
  (suc↦-intro₁ (⊑ₙ-intro₃ y′⊑sx′)) (conₙ-sₙ conxx′)
  = conₙ-sₙ (suc↦-con (suc↦-intro₁ y⊑sx) (suc↦-intro₁ y′⊑sx′) conxx′)
