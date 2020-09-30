{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.ap.Instance where

open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.LambdaBeta.ap.AxiomProofs
open import Ucwf.DomainUcwf.LambdaBeta.ap.Relation
open import Ucwf.DomainUcwf.UniType.Definition

ap : uAppmap n 1 → uAppmap n 1 → uAppmap n 1
Appmap._↦_ (ap 𝑡 𝑢)         = [_,_]_ap↦_ 𝑡 𝑢
Appmap.↦-mono (ap 𝑡 𝑢)      = ap↦-mono
Appmap.↦-bottom (ap 𝑡 𝑢)    = ap↦-bottom
Appmap.↦-↓closed (ap 𝑡 𝑢)   = ap↦-↓closed
Appmap.↦-↑directed (ap 𝑡 𝑢) = ap↦-↑directed
Appmap.↦-con (ap 𝑡 𝑢)       = ap↦-con
