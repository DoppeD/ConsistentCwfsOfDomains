{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.Appmap.Definition where

open import Scwf.DomainScwf.Appmap.Definition public
open import Ucwf.DomainUcwf.UniType.Instance

open import Agda.Builtin.Nat

uSub : Nat → Nat → Set₁
uSub m n = Sub (nToCtx m) (nToCtx n)

uTerm : Nat → Set₁
uTerm n = Term (nToCtx n) UniType
