module Nat.zero.AxiomProofs where

open import Nat.NbhSys.AxiomProofs
open import Nat.NbhSys.Definition
open import Nat.NbhSys.Instance
open import Nat.NbhSys.Relation
open import Nat.zero.Relation

zero↦-mono : ∀ {x y z} → x ⊑ₙ y → x zero↦ z →
               y zero↦ z
zero↦-mono x⊑y (zero-intro ⊑ₙ-intro₁)
  = zero-intro ⊑ₙ-intro₁
zero↦-mono x⊑y (zero-intro ⊑ₙ-intro₂)
  = zero-intro ⊑ₙ-intro₂

zero↦-bottom : ∀ {x} → x zero↦ ⊥ₙ
zero↦-bottom = zero-intro ⊑ₙ-intro₁

zero↦-↓closed : ∀ {x y z} → y ⊑ₙ z → x zero↦ z →
                x zero↦ y
zero↦-↓closed y⊑z (zero-intro ⊑ₙ-intro₂)
  = zero-intro y⊑z
zero↦-↓closed ⊑ₙ-intro₁ (zero-intro ⊑ₙ-intro₁)
  = zero-intro ⊑ₙ-intro₁

zero↦-↑directed : ∀ {x y z} → x zero↦ y → x zero↦ z →
                  ∀ conyz → x zero↦ (y ⊔ₙ z [ conyz ])
zero↦-↑directed (zero-intro y⊑0) (zero-intro z⊑0) conyz
  = zero-intro y⊔z⊑0
  where y⊔z⊑0 = ⊑ₙ-⊔ y⊑0 z⊑0 conyz

zero↦-con : ∀ {x x′ y y′} → x zero↦ y → x′ zero↦ y′ →
            Conₙ x x′ → Conₙ y y′
zero↦-con (zero-intro ⊑ₙ-intro₁) (zero-intro _) _
  = conₙ-bot₁
zero↦-con (zero-intro ⊑ₙ-intro₂) (zero-intro ⊑ₙ-intro₁) _
  = conₙ-bot₂
zero↦-con (zero-intro ⊑ₙ-intro₂) (zero-intro ⊑ₙ-intro₂) _
  = conₙ-0ₙ
