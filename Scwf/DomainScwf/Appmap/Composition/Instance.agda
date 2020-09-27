{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Composition.Instance where

open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Composition.AxiomProofs
open import Scwf.DomainScwf.Appmap.Composition.Relation

_∘_ : tAppmap Δ Θ → tAppmap Γ Δ → tAppmap Γ Θ
Appmap._↦_ (δ ∘ γ)         = _∘↦_ δ γ
Appmap.↦-mono (δ ∘ γ)      = ∘↦-mono δ γ
Appmap.↦-bottom (δ ∘ γ)    = ∘↦-bottom δ γ
Appmap.↦-↓closed (δ ∘ γ)   = ∘↦-↓closed δ γ
Appmap.↦-↑directed (δ ∘ γ) = ∘↦-↑directed δ γ
Appmap.↦-con (δ ∘ γ)       = ∘↦-con δ γ
