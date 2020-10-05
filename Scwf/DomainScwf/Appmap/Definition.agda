{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Definition where

open import Appmap.Definition public
open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

Sub : (Γ : Ctx m) → (Δ : Ctx n) → Set₁
Sub Γ Δ = Appmap (ValNbhSys Γ) (ValNbhSys Δ)

Term : (Γ : Ctx m) → (𝐴 : Ty) → Set₁
Term Γ 𝐴 = Appmap (ValNbhSys Γ) 𝐴
