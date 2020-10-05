module Nat.pred.Relation where

open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation

data _pred↦_ : NatNbh → NatNbh → Set where
  pred↦-intro₁ : ∀ {x} → x pred↦ ⊥ₙ
  pred↦-intro₂ : ∀ {x y} → (sₙ y) ⊑ₙ x → x pred↦ y
