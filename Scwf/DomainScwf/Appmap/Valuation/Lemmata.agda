{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Valuation.Lemmata where

open import Base.Core
open import Base.Variables
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition

valConRefl : ∀ {x} → ValCon Γ x x
valConRefl {x = ⟪⟫} = con-nil
valConRefl {Γ = 𝐴 :: Γ} {x = ⟪ x , 𝑥 ⟫}
  = con-tup x x (conRefl 𝐴) 𝑥 𝑥 valConRefl
