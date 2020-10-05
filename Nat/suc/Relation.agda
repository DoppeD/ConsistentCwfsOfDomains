module Nat.suc.Relation where

open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation

data _suc↦_ : NatNbh → NatNbh → Set where
  suc↦-intro : ∀ {x y} → y ⊑ₙ (sₙ x) → x suc↦ y
