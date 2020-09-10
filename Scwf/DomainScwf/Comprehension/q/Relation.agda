{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.q.Relation where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition

data _q↦_ : Valuation (𝐴 :: Γ) → Valuation [ 𝐴 ] → Set where
  q↦-intro : (𝑥 : Valuation (𝐴 :: Γ)) →
             (𝑦 : Valuation [ 𝐴 ]) →
             [ 𝐴 ] (ctHead 𝑦) ⊑ (ctHead 𝑥) → 𝑥 q↦ 𝑦
