{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.Appmap.Definition where

open import Scwf.DomainScwf.Appmap.Definition public
open import Ucwf.DomainUcwf.UniType.Instance

open import Agda.Builtin.Nat

-- Notation for approximable mappings between
-- neighborhoods of the universal type.
uAppmap : Nat → Nat → Set₁
uAppmap m n = tAppmap (nToCtx m) (nToCtx n)
