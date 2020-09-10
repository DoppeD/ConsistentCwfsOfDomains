{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.Morphism.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Comprehension.Morphism.AxiomProofs
open import Scwf.DomainScwf.Comprehension.Morphism.Relation

⟨_,_⟩ : tAppmap Δ Γ → tAppmap Δ [ 𝐴 ] → tAppmap Δ (𝐴 :: Γ)
Appmap._↦_ ⟨ γ , 𝑡 ⟩         = ⟨⟩↦ γ 𝑡
Appmap.↦-mono ⟨ γ , 𝑡 ⟩      = ⟨⟩↦-mono γ 𝑡
Appmap.↦-bottom ⟨ γ , 𝑡 ⟩    = ⟨⟩↦-bottom γ 𝑡
Appmap.↦-↓closed ⟨ γ , 𝑡 ⟩   = ⟨⟩↦-↓closed γ 𝑡
Appmap.↦-↑directed ⟨ γ , 𝑡 ⟩ = ⟨⟩↦-↑directed γ 𝑡
