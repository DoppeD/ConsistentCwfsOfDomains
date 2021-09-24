module Cwf.DomainCwf.UniType.Consistency where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Definition

-- See ConsistencyTerminating for a proof that this is terminating.
-- We use the definition below that doesn't use an accessibility predicate
-- in order to not have to carry around and manipulate such a predicate.

{-# TERMINATING #-}
con : ∀ u → Set
conFinFun : ∀ f → Set

con ⊥ = 𝟙
con 0ᵤ = 𝟙
con (s u) = con u
con ℕ = 𝟙
con (F f) = conFinFun f
con (refl u) = con u
con (I U u u′) = con U ⊠ (con u ⊠ con u′)
con (Π U f) = con U ⊠ conFinFun f
con 𝒰 = 𝟙
con incons = 𝟘

-- A finite function is consistent if:
-- a) For any pairs (u , v) ∈ f and (u′ , v′) ∈ f, if (u ⊔ u′) is consistent then so is (v ⊔ v′)
-- b) For any pair (u , v) ∈ f, both u and v are themselves consistent.
conFinFun f =
  (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → con (u ⊔ u′) → con (v ⊔ v′)) ⊠
  (∀ {u v} → (u , v) ∈ f → con u ⊠ con v)
