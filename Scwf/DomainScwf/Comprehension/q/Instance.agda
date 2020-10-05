{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.q.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Comprehension.q.AxiomProofs
open import Scwf.DomainScwf.Comprehension.q.Relation

q : (Γ : Ctx n) → (𝐴 : Ty) → Term (𝐴 :: Γ) 𝐴
Appmap._↦_ (q Γ 𝐴)         = _q↦_
Appmap.↦-mono (q Γ 𝐴)      = q↦-mono
Appmap.↦-bottom (q Γ 𝐴)    = q↦-bottom
Appmap.↦-↓closed (q Γ 𝐴)   = q↦-↓closed
Appmap.↦-↑directed (q Γ 𝐴) = q↦-↑directed
Appmap.↦-con (q Γ 𝐴)       = q↦-con
