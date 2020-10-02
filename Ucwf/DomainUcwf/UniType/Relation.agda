{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.Relation where

open import Base.Core hiding (_,_)
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.PrePost
open import Ucwf.DomainUcwf.UniType.SizedFinFun

open import Agda.Builtin.Size

private
  variable i j : Size

record ⊑ᵤ-proof {i j : Size} (𝑓 : FinFunₛ {j})
                (x y : UniNbh {i}) : Set

data _⊑ᵤ_ : UniNbh {i} → UniNbh {j} → Set

record ⊑ᵤ-proof 𝑓 x y where
  inductive
  field
    sub : FinFunₛ
    y⊑ᵤpost : y ⊑ᵤ (post sub)
    pre⊑ᵤx : (pre sub) ⊑ᵤ x
    sub⊆𝑓′ : sub ⊆ₛ 𝑓

data _⊑ᵤ_ where
  ⊑ᵤ-intro₁ : ∀ {i j} → {x : UniNbh {j}} →
              (⊥ᵤ {i}) ⊑ᵤ x
  ⊑ᵤ-intro₂ : ∀ {i j} → (𝑓 : FinFunₛ {i}) →
              (𝑓′ : FinFunₛ {j}) →
              ((x y : UniNbh {i}) → (x , y) ∈ₛ 𝑓 →
              ⊑ᵤ-proof {i} {j} 𝑓′ x y) →
              _⊑ᵤ_ {↑ i} {↑ j} (λᵤ 𝑓) (λᵤ 𝑓′)
