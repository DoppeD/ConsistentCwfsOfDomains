{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.ap.Instance where

open import Base.Variables
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.ap.AxiomProofs
open import Ucwf.DomainUcwf.LambdaBeta.ap.Relation
open import Ucwf.DomainUcwf.UniType.Definition

ap : uTerm n → uTerm n → uTerm n
Appmap._↦_ (ap 𝑡 𝑢)         = [_,_]_ap↦_ 𝑡 𝑢
Appmap.↦-mono (ap 𝑡 𝑢)      = ap↦-mono
Appmap.↦-bottom (ap 𝑡 𝑢)    = ap↦-bottom
Appmap.↦-↓closed (ap 𝑡 𝑢)   = ap↦-↓closed
Appmap.↦-↑directed (ap 𝑡 𝑢) = ap↦-↑directed
Appmap.↦-con (ap 𝑡 𝑢)       = λ _ _ _ → con-all
