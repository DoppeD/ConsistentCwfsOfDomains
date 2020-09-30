{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.lamCong where

open import Appmap.Equivalence
open import Base.Core
open import Base.Variables
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.lam.Instance
open import Ucwf.DomainUcwf.LambdaBeta.lam.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance

open import Agda.Builtin.Nat

private
  variable
    𝑡 𝑡′ : uAppmap (suc n) 1

lamCongLemma : 𝑡 ≼ 𝑡′ → ∀ {𝑥 𝑦} → [ lam 𝑡 ] 𝑥 ↦ 𝑦 →
               [ lam 𝑡′ ] 𝑥 ↦ 𝑦
lamCongLemma _ {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} _ = lam↦-intro₁
lamCongLemma (≼-intro p₁) {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫}
  (lam↦-intro₂ _ _ p₂)
  = lam↦-intro₂ _ _ λ x y xy∈𝑓 → p₁ (p₂ x y xy∈𝑓)

lamCong : 𝑡 ≈ 𝑡′ → lam 𝑡 ≈ lam 𝑡′
lamCong (≈-intro 𝑡≼𝑡′ 𝑡′≼𝑡)
  = ≈-intro (≼-intro (lamCongLemma 𝑡≼𝑡′))
            (≼-intro (lamCongLemma 𝑡′≼𝑡))
