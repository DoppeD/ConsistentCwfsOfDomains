{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Definition where

open import Appmap.Definition public
open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

-- Some simplifying notation for approximable mappings in
-- our scwf.
tAppmap : (Γ : Ctx m) → (Δ : Ctx n) → Set₁
tAppmap Γ Δ = Appmap (ValNbhSys Γ) (ValNbhSys Δ)
