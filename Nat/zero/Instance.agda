module Nat.zero.Instance where

open import Appmap.Definition
open import Nat.NbhSys.Instance
open import Nat.zero.AxiomProofs
open import Nat.zero.Relation

zero : Appmap NatNbhSys NatNbhSys
Appmap._↦_ zero = _zero↦_
Appmap.↦-mono zero = zero↦-mono
Appmap.↦-bottom zero = zero↦-bottom
Appmap.↦-↓closed zero = zero↦-↓closed
Appmap.↦-↑directed zero = zero↦-↑directed
Appmap.↦-con zero = zero↦-con
