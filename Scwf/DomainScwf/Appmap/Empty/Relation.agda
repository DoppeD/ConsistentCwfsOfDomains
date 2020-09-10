{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Empty.Relation where

open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Base.Core
open import Base.Variables

data _empty↦_ : Valuation Γ → Valuation [] → Set where
  empty↦-intro : {𝑥 : Valuation Γ} → 𝑥 empty↦ ⟪⟫
