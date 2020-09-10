{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.lam.Relation where

open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.SizedFinFun

open import Agda.Builtin.Nat

private
  variable
    n : Nat

data [_]_lam↦_ (𝑡 : uAppmap (suc n) 1) :
               uValuation n → uValuation 1 → Set where
  lam↦-intro₁ : ∀ {𝑥} → [ 𝑡 ] 𝑥 lam↦ ⟪ ⊥ᵤ ⟫
  lam↦-intro₂ : ∀ 𝑥 𝑓 →
                (∀ x y → < x , y >ₛ ∈ₛ 𝑓 →
                [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫) →
                [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓 ⟫
