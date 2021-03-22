{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.Consistency where

open import Base.Core
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun

con : ∀ {i} → Nbh {i} -> Set
conFinFun : ∀ {i} → FinFun {i} → Set
con ⊥ = 𝟙
con 0ᵤ = 𝟙
con (s u) = con u
con ℕ = 𝟙
con (F f) = conFinFun f
con (refl u) = con u
con (Π u f) = con u ⊠ conFinFun f
con 𝒰 = 𝟙
con incons = 𝟘

conFinFun f
  = (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → con (u ⊔ u′) → con (v ⊔ v′))
    ⊠
    (∀ {u v} → (u , v) ∈ f → con u ⊠ con v)
