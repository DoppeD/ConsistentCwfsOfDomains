{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.p.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Comprehension.p.AxiomProofs
open import Scwf.DomainScwf.Comprehension.p.Relation

p : (Γ : Ctx n) → (𝐴 : Ty) → tAppmap (𝐴 :: Γ) Γ
Appmap._↦_ (p Γ 𝐴)         = _p↦_
Appmap.↦-mono (p Γ 𝐴)      = p↦-mono
Appmap.↦-bottom (p Γ 𝐴)    = p↦-bottom
Appmap.↦-↓closed (p Γ 𝐴)   = p↦-↓closed
Appmap.↦-↑directed (p Γ 𝐴) = p↦-↑directed
Appmap.↦-con (p Γ 𝐴)       = p↦-con
