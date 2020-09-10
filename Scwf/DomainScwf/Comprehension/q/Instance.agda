{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.q.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Comprehension.q.AxiomProofs
open import Scwf.DomainScwf.Comprehension.q.Relation

q : (Γ : Ctx n) → (𝐴 : Ty) → tAppmap (𝐴 :: Γ) [ 𝐴 ]
Appmap._↦_ (q Γ A)         = _q↦_
Appmap.↦-mono (q Γ A)      = q↦-mono
Appmap.↦-bottom (q Γ A)    = q↦-bottom
Appmap.↦-↓closed (q Γ A)   = q↦-↓closed
Appmap.↦-↑directed (q Γ A) = q↦-↑directed
