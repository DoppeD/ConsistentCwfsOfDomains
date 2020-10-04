module Nat.suc.Instance where

suc : Appmap NatNbhSys NatNbhSys
Appmap._↦_ suc         = _suc↦_
Appmap.↦-mono suc      = suc↦-mono
Appmap.↦-bottom suc    = suc↦-intro₁ ⊑ₙ-intro₁
Appmap.↦-↓closed suc   = suc↦-↓closed
Appmap.↦-↑directed suc = suc↦-↑directed
Appmap.↦-con suc       = suc↦-con
