{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Identity.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Identity.AxiomProofs
open import Scwf.DomainScwf.Appmap.Identity.Relation

idMap : (Γ : Ctx n) → Sub Γ Γ
Appmap._↦_ (idMap Γ)         = _id↦_
Appmap.↦-mono (idMap Γ)      = id↦-mono
Appmap.↦-bottom (idMap Γ)    = id↦-bottom
Appmap.↦-↓closed (idMap Γ)   = id↦-↓closed
Appmap.↦-↑directed (idMap Γ) = id↦-↑directed
Appmap.↦-con (idMap Γ)       = id↦-con
