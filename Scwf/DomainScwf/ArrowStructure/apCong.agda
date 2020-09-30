{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.apCong (𝐴 𝐵 : Ty) where

open import Appmap.Definition
open import Appmap.Equivalence
open import Base.Variables hiding (𝐴 ; 𝐵)
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

private
  variable
    𝑡 𝑡′ : tAppmap Γ [ ArrNbhSys 𝐴 𝐵 ]
    𝑢 𝑢′ : tAppmap Γ [ 𝐴 ]

apCongLemma : 𝑡 ≼ 𝑡′ → 𝑢 ≼ 𝑢′ → ∀ 𝑥 𝑦 →
              [ ap 𝑡 𝑢 ] 𝑥 ↦ 𝑦 → [ ap 𝑡′ 𝑢′ ] 𝑥 ↦ 𝑦
apCongLemma (≼-intro 𝑡≼𝑡′) (≼-intro 𝑢≼𝑢′) 𝑥 ⟪ y , ⟪⟫ ⟫
  (ap↦-intro₁ p)
  = ap↦-intro₁ p
apCongLemma (≼-intro 𝑡≼𝑡′) (≼-intro 𝑢≼𝑢′) 𝑥 ⟪ y , ⟪⟫ ⟫
  (ap↦-intro₂ {z} {𝑓 = 𝑓} _ _ 𝑡𝑥↦𝑓 𝑢𝑥↦z zy⊑𝑓)
  = ap↦-intro₂ _ _ (𝑡≼𝑡′ 𝑥 ⟪ 𝐹 𝑓 _ ⟫ 𝑡𝑥↦𝑓)
    (𝑢≼𝑢′ 𝑥 ⟪ z ⟫ 𝑢𝑥↦z) zy⊑𝑓

apCong : 𝑡 ≈ 𝑡′ → 𝑢 ≈ 𝑢′ →
         ap 𝑡 𝑢 ≈ ap 𝑡′ 𝑢′
apCong (≈-intro 𝑡≼𝑡′ 𝑡′≼𝑡) (≈-intro 𝑢≼𝑢′ 𝑢′≼𝑢)
  = ≈-intro (≼-intro (apCongLemma 𝑡≼𝑡′ 𝑢≼𝑢′))
            (≼-intro (apCongLemma 𝑡′≼𝑡 𝑢′≼𝑢))
