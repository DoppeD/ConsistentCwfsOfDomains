{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.ap.Relation where

open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.SizedFinFun

open import Agda.Builtin.Nat

private
  variable
    n : Nat

data [_,_]_ap↦_ (𝑡 𝑢 : uAppmap n 1) (𝑥 : uValuation n) :
                uValuation 1 → Set where
  ap↦-intro₁ : [ 𝑡 , 𝑢 ] 𝑥 ap↦ ⟪ ⊥ᵤ ⟫
  ap↦-intro₂ : ∀ {x y 𝑓} →
               [ 𝑡 ] 𝑥 ↦ ⟪ λᵤ 𝑓 ⟫ → [ 𝑢 ] 𝑥 ↦ ⟪ x ⟫ →
               (λᵤ (< x , y >ₛ ∷ ∅)) ⊑ᵤ (λᵤ 𝑓) →
               [ 𝑡 , 𝑢 ] 𝑥 ap↦ ⟪ y ⟫
