{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.q.Relation where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition

data _q↦_ : Valuation (𝐴 :: Γ) → NbhSys.Nbh 𝐴 → Set where
  q↦-intro : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {y} →
             [ 𝐴 ] y ⊑ (ctHead 𝑥) → 𝑥 q↦ y
