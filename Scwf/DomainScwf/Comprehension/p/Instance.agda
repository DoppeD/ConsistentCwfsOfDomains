{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.p.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Comprehension.p.AxiomProofs
open import Scwf.DomainScwf.Comprehension.p.Relation

p : (Γ : Ctx n) → (𝐴 : Ty) → tAppmap (𝐴 :: Γ) Γ
Appmap._↦_ (p Γ A)         = _p↦_
Appmap.↦-mono (p Γ A)      = p↦-mono
Appmap.↦-bottom (p Γ A)    = p↦-bottom
Appmap.↦-↓closed (p Γ A)   = p↦-↓closed
Appmap.↦-↑directed (p Γ A) = p↦-↑directed
