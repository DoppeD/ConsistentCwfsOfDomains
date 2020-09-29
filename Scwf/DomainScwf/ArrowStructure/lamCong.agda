{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.lamCong (𝐴 𝐵 : Ty) where

open import Appmap.Equivalence
open import Base.Variables hiding (𝐴 ; 𝐵)
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.lam.Instance
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

lamCongLemma : {𝑡 𝑡′ : tAppmap (𝐴 :: Γ) [ 𝐵 ]} →
               𝑡 ≼ 𝑡′ → ∀ 𝑥 𝑦 →
               [ lam 𝑡 ] 𝑥 ↦ 𝑦 → [ lam 𝑡′ ] 𝑥 ↦ 𝑦
lamCongLemma (≼-intro p₁) 𝑥 ⟪ ⊥ₑ , ⟪⟫ ⟫ lam↦-intro₁
  = lam↦-intro₁
lamCongLemma (≼-intro p₁) 𝑥 ⟪ 𝐹 𝑓 _ , ⟪⟫ ⟫
  (lam↦-intro₂ _ _ _ p₂)
  = lam↦-intro₂ 𝑥 𝑓 _ (λ x y xy∈𝑓 → p₁ ⟪ x , 𝑥 ⟫ ⟪ y ⟫
    (p₂ x y xy∈𝑓))

lamCong : {𝑡 𝑡′ : tAppmap (𝐴 :: Γ) [ 𝐵 ]} → 𝑡 ≈ 𝑡′ →
          lam 𝑡 ≈ lam 𝑡′
lamCong (≈-intro 𝑡≼𝑡′ 𝑡′≼𝑡)
  = ≈-intro (≼-intro (lamCongLemma 𝑡≼𝑡′))
            (≼-intro (lamCongLemma 𝑡′≼𝑡))
