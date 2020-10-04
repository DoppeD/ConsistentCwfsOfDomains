module Nat.pred.Relation where

open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation

data _pred↦_ : NatNbh → NatNbh → Set where
  pred↦-intro₁ : ∀ {x y} → x ⊑ₙ 0ₙ → y ⊑ₙ x → x pred↦ y
  pred↦-intro₂ : ∀ {x y} → (sₙ ⊥ₙ) ⊑ₙ x → (sₙ y) ⊑ₙ x → x pred↦ y
