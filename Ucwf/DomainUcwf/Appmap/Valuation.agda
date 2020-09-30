{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.Appmap.Valuation where

open import Scwf.DomainScwf.Appmap.Valuation.Definition public
open import Scwf.DomainScwf.Appmap.Valuation.Instance public
open import Scwf.DomainScwf.Appmap.Valuation.Relation public
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance

open import Agda.Builtin.Nat

-- Notation for valuations of contexts in the ucwf.
uValuation : Nat → Set
uValuation n = Valuation (nToCtx n)

valConAll : ∀ {n 𝑥 𝑦} → ValCon (nToCtx n) 𝑥 𝑦
valConAll {𝑥 = ⟪⟫} {⟪⟫} = con-nil
valConAll {𝑥 = ⟪ _ ,, _ ⟫} {⟪ _ ,, _ ⟫}
  = con-tup con-all valConAll
