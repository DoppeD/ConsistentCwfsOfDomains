{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.lam.Instance where

open import Base.Variables
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.lam.AxiomProofs
open import Ucwf.DomainUcwf.LambdaBeta.lam.Relation

open import Agda.Builtin.Nat

lam : uAppmap (suc n) 1 → uAppmap n 1
Appmap._↦_ (lam 𝑡)         = [_]_lam↦_ 𝑡
Appmap.↦-mono (lam 𝑡)      = lam↦-mono
Appmap.↦-bottom (lam 𝑡)    = lam↦-bottom
Appmap.↦-↓closed (lam 𝑡)   = lam↦-↓closed
Appmap.↦-↑directed (lam 𝑡) = lam↦-↑directed
Appmap.↦-con (lam 𝑡)       = λ _ _ _ → valConAll
