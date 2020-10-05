{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.snd.Relation where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

data snd↦ (𝑡 : Term Γ (𝐴 × 𝐵)) :
          Valuation Γ → NbhSys.Nbh 𝐵 → Set where
  snd-intro₁ : ∀ {𝑥 y} → [ 𝐵 ] y ⊑ NbhSys.⊥ 𝐵 → snd↦ 𝑡 𝑥 y
  snd-intro₂ : ∀ {𝑥 y₁ y₂} → [ 𝑡 ] 𝑥 ↦ < y₁ , y₂ > →
               snd↦ 𝑡 𝑥 y₂
