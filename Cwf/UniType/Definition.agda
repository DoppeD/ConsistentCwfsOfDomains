module Cwf.UniType.Definition where

open import Base.FinFun

open import Agda.Builtin.Size

data Nbh : {Size} → Set where
  ⊥ : ∀ {i} → Nbh {i}
  0ₙ : ∀ {i} → Nbh {i}
  sᵤ : ∀ {i} → Nbh {i} → Nbh {i}
  ℕ : ∀ {i} → Nbh {i}
  𝒰 : ∀ {i} → Nbh {i}
  λᵤ : ∀ {i} → FinFun (Nbh {i}) (Nbh {i}) → Nbh {↑ i}
  Π : ∀ {i} → Nbh {i} → FinFun (Nbh {i}) (Nbh {i}) → Nbh {↑ i}
