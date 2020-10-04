module Nat.NbhSys.Relation where

open import Nat.NbhSys.Definition

data _⊑ₙ_ : NatNbh → NatNbh → Set where
  ⊑ₙ-intro₁ : ∀ {x} → ⊥ₙ ⊑ₙ x
  ⊑ₙ-intro₂ : 0ₙ ⊑ₙ 0ₙ
  ⊑ₙ-intro₃ : ∀ {x y} → x ⊑ₙ y → sₙ x ⊑ₙ sₙ y
