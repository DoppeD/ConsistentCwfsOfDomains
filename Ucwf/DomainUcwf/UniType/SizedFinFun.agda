{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.SizedFinFun where

open import Base.Core
open import Ucwf.DomainUcwf.UniType.Definition

open import Agda.Builtin.Size
open import Agda.Primitive

private
  variable
    𝑓 𝑓′ 𝑓″ 𝑓‴ : FinFunₛ

data _∈ₛ_ : {i : Size} → ×ₛ {i} → FinFunₛ {i} → Set where
  here : {i : Size} → {x : ×ₛ {i}} → {𝑓 : FinFunₛ {i}} →
         x ∈ₛ (x ∷ 𝑓)
  there : {i : Size} → {x x' : ×ₛ {i}} → {𝑓 : FinFunₛ {i}} →
          x ∈ₛ 𝑓 → x ∈ₛ (x' ∷ 𝑓)

_⊆ₛ_ : {i : Size} → FinFunₛ {i} → FinFunₛ {i} → Set
_⊆ₛ_ {i} 𝑓 𝑓′ = ∀ x → _∈ₛ_ {i} x 𝑓 → _∈ₛ_ {i} x 𝑓′

⊆ₛ-refl : {i : Size} → {𝑓 : FinFunₛ {i}} → 𝑓 ⊆ₛ 𝑓
⊆ₛ-refl x x∈𝑓 = x∈𝑓

⊆ₛ-trans : {i : Size} → {𝑓 𝑓′ 𝑓″ : FinFunₛ {i}} → 𝑓 ⊆ₛ 𝑓′ →
           𝑓′ ⊆ₛ 𝑓″ → 𝑓 ⊆ₛ 𝑓″
⊆ₛ-trans 𝑓⊆𝑓′ 𝑓′⊆𝑓″ x x∈𝑓 = 𝑓′⊆𝑓″ x (𝑓⊆𝑓′ x x∈𝑓)

⊆ₛ-lemma₃ : {i : Size} → ∀ {x} → {𝑓 : FinFunₛ {i}} →
            𝑓 ⊆ₛ (x ∷ 𝑓)
⊆ₛ-lemma₃ y y∈𝑓 = there y∈𝑓

⊆ₛ-lemma₄ : ∀ {x} → x ∈ₛ 𝑓 → 𝑓′ ⊆ₛ 𝑓 → (x ∷ 𝑓′) ⊆ₛ 𝑓
⊆ₛ-lemma₄ x∈𝑓 _ _ here = x∈𝑓
⊆ₛ-lemma₄ x∈𝑓 𝑓′⊆𝑓 y (there y∈𝑓) = 𝑓′⊆𝑓 y y∈𝑓

∅-isSubsetₛ : {i : Size} → {𝑓 : FinFunₛ {i}} → ∅ ⊆ₛ 𝑓
∅-isSubsetₛ x ()

∪ₛ-lemma₁ : {i : Size} → {𝑓 𝑓′ 𝑓″ : FinFunₛ {i}} →
            𝑓 ⊆ₛ 𝑓″ → 𝑓′ ⊆ₛ 𝑓″ → (𝑓 ∪ₛ 𝑓′) ⊆ₛ 𝑓″
∪ₛ-lemma₁ {𝑓 = ∅} _ 𝑓′⊆𝑓″ y y∈𝑓∪𝑓′ = 𝑓′⊆𝑓″ y y∈𝑓∪𝑓′
∪ₛ-lemma₁ {𝑓 = x ∷ _} 𝑓⊆𝑓″ _ _ here = 𝑓⊆𝑓″ x here
∪ₛ-lemma₁ {𝑓 = x ∷ 𝑓‴} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ y (there y∈𝑓∪𝑓′)
  = ∪ₛ-lemma₁ (⊆ₛ-trans ⊆ₛ-lemma₃ 𝑓⊆𝑓″) 𝑓′⊆𝑓″ y y∈𝑓∪𝑓′

∪ₛ-lemma₂ : {i : Size} → {𝑓 𝑓′ : FinFunₛ {i}} → ∀ x →
            x ∈ₛ (𝑓 ∪ₛ 𝑓′) → (x ∈ₛ 𝑓) ∨ (x ∈ₛ 𝑓′)
∪ₛ-lemma₂ {𝑓 = ∅} _ here = inr here
∪ₛ-lemma₂ {𝑓 = ∅} _ (there x∈xs) = inr (there x∈xs)
∪ₛ-lemma₂ {𝑓 = x ∷ _} _ here = inl here
∪ₛ-lemma₂ {𝑓 = x ∷ 𝑓″} y (there y∈∪)
  with (∪ₛ-lemma₂ y y∈∪)
∪ₛ-lemma₂ y (there y∈∪) | inl y∈𝑓″ = inl (there y∈𝑓″)
∪ₛ-lemma₂ y (there y∈∪) | inr y∈𝑓′ = inr y∈𝑓′

∪ₛ-lemma₃ : {i : Size} → {𝑓 𝑓′ : FinFunₛ {i}} → ∀ x →
            x ∈ₛ 𝑓 → x ∈ₛ (𝑓 ∪ₛ 𝑓′)
∪ₛ-lemma₃ {𝑓 = x ∷ 𝑓″} _ here = here
∪ₛ-lemma₃ {𝑓 = x ∷ 𝑓″} y (there y∈𝑓″) = ⊆ₛ-lemma₃ y y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪ₛ-lemma₃ y y∈𝑓″

∪ₛ-lemma₄ : {i : Size} → {𝑓 𝑓′ : FinFunₛ {i}} → ∀ x →
            x ∈ₛ 𝑓′ → x ∈ₛ (𝑓 ∪ₛ 𝑓′)
∪ₛ-lemma₄ {𝑓 = ∅} x x∈𝑓′ = x∈𝑓′
∪ₛ-lemma₄ {𝑓 = x ∷ 𝑓″} y y∈𝑓′ = ⊆ₛ-lemma₃ y y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪ₛ-lemma₄ y y∈𝑓′

∪ₛ-lemma₅ : 𝑓 ⊆ₛ 𝑓″ → 𝑓′ ⊆ₛ 𝑓‴ → (𝑓 ∪ₛ 𝑓′) ⊆ₛ (𝑓″ ∪ₛ 𝑓‴)
∪ₛ-lemma₅ _ _ x x∈𝑓∪𝑓′ with (∪ₛ-lemma₂ x x∈𝑓∪𝑓′)
∪ₛ-lemma₅ 𝑓⊆𝑓″ _ x _ | inl x∈𝑓 = ∪ₛ-lemma₃ x (𝑓⊆𝑓″ x x∈𝑓)
∪ₛ-lemma₅ _ 𝑓′⊆𝑓‴ x _ | inr x∈𝑓′ = ∪ₛ-lemma₄ x (𝑓′⊆𝑓‴ x x∈𝑓′)

-- From a proof that a pair of neighborhoods is
-- in the empty set, anything.
xy∈∅-abs : {p : Set} → ∀ {x y} → < x , y >ₛ ∈ₛ ∅ → p
xy∈∅-abs ()
