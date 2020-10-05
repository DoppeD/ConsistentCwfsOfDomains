module Nat.suc.AxiomProofs where

open import Nat.NbhSys.AxiomProofs
open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation
open import Nat.suc.Relation

suc↦-mono : ∀ {x y z} → x ⊑ₙ y → x suc↦ z →
            y suc↦ z
suc↦-mono x⊑y (suc↦-intro z⊑x)
  = suc↦-intro (⊑ₙ-trans z⊑x (⊑ₙ-intro₃ x⊑y))

suc↦-bottom : ∀ {x} → x suc↦ ⊥ₙ
suc↦-bottom = suc↦-intro ⊑ₙ-intro₁

suc↦-↓closed : ∀ {x y z} → y ⊑ₙ z → x suc↦ z →
               x suc↦ y
suc↦-↓closed y⊑x (suc↦-intro z⊑sx)
  = suc↦-intro (⊑ₙ-trans y⊑x z⊑sx)

suc↦-↑directed : ∀ {x y z} → x suc↦ y → x suc↦ z →
                 ∀ conyz → x suc↦ (y ⊔ₙ z [ conyz ])
suc↦-↑directed (suc↦-intro y⊑sx) (suc↦-intro z⊑sx) conyz
  = suc↦-intro (⊑ₙ-⊔ y⊑sx z⊑sx conyz)

suc↦-con : ∀ {x y x′ y′} → x suc↦ y → x′ suc↦ y′ →
           Conₙ x x′ → Conₙ y y′
suc↦-con (suc↦-intro y⊑sx) (suc↦-intro y′⊑sx′) conxx′
  = Conₙ-⊔ y⊑sx⊔sx′ y′⊑sx⊔sx′
  where consxsx′ = conₙ-sₙ conxx′
        y⊑sx⊔sx′ = ⊑ₙ-trans y⊑sx (⊑ₙ-⊔-fst consxsx′)
        y′⊑sx⊔sx′ = ⊑ₙ-trans y′⊑sx′ (⊑ₙ-⊔-snd consxsx′)
