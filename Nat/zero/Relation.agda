module Nat.zero.Relation where

open import Nat.NbhSys.Definition
open import Nat.NbhSys.Relation

data _zero↦_ : NatNbh → NatNbh → Set where
  zero-intro : ∀ {x y} → y ⊑ₙ 0ₙ → x zero↦ y
