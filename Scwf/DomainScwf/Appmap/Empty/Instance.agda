{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Empty.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Empty.AxiomProofs
open import Scwf.DomainScwf.Appmap.Empty.Relation
open import Scwf.DomainScwf.Appmap.Definition

emptyMap : Sub Γ []
Appmap._↦_ (emptyMap)         = _empty↦_
Appmap.↦-mono (emptyMap)      = empty↦-mono
Appmap.↦-bottom (emptyMap)    = empty↦-intro
Appmap.↦-↓closed (emptyMap)   = empty↦-↓closed
Appmap.↦-↑directed (emptyMap) = empty↦-↑directed
Appmap.↦-con (emptyMap)       = empty↦-con
