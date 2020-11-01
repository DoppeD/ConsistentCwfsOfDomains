{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.Relation where

open import Base.Core
open import Base.FinFun
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.PrePost

open import Agda.Builtin.Size

private
  variable i j : Size

record ⊑ᵤ-proof {i : Size} (𝑓 : FinFunₛ {i})
                (x y : UniNbh {i}) : Set

data _⊑ᵤ_ : UniNbh {i} → UniNbh {i} → Set

record ⊑ᵤ-proof 𝑓 x y where
  inductive
  field
    sub : FinFunₛ
    y⊑ᵤpost : y ⊑ᵤ (post sub)
    pre⊑ᵤx : (pre sub) ⊑ᵤ x
    sub⊆𝑓′ : sub ⊆ 𝑓

data _⊑ᵤ_ where
  ⊑ᵤ-intro₁ : ∀ {i} → {x : UniNbh {i}} →
              ⊥ᵤ ⊑ᵤ x
  ⊑ᵤ-intro₂ : ∀ {i} → (𝑓 : FinFunₛ {i}) →
              (𝑓′ : FinFunₛ {i}) →
              ((x y : UniNbh {i}) → (x , y) ∈ 𝑓 →
              ⊑ᵤ-proof {i} 𝑓′ x y) →
              _⊑ᵤ_ {↑ i} (λᵤ 𝑓) (λᵤ 𝑓′)
