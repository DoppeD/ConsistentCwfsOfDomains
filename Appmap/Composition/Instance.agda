{-# OPTIONS --safe #-}

module Appmap.Composition.Instance where

open import Appmap.Definition
open import Appmap.Composition.AxiomProofs
open import Appmap.Composition.Relation
open import Base.Variables

_∘_ : Appmap 𝐵 𝐶 → Appmap 𝐴 𝐵 → Appmap 𝐴 𝐶
Appmap._↦_ (δ ∘ γ)         = _∘↦_ δ γ
Appmap.↦-mono (δ ∘ γ)      = ∘↦-mono δ γ
Appmap.↦-bottom (δ ∘ γ)    = ∘↦-bottom δ γ
Appmap.↦-↓closed (δ ∘ γ)   = ∘↦-↓closed δ γ
Appmap.↦-↑directed (δ ∘ γ) = ∘↦-↑directed δ γ
Appmap.↦-con (δ ∘ γ)       = ∘↦-con δ γ
