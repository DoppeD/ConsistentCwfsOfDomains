module Cwf.UniType.FinFun where

open import Base.Core
--open import Base.Variables
open import Cwf.UniType.Definition

data _∈_ : ∀ {i} → (Nbh {i}) ⊠ (Nbh {i}) → FinFun {i} → Set where
  here : ∀ {i} → {x : Nbh {i} ⊠ Nbh {i}} → ∀ {𝑓} → x ∈ (x ∷ 𝑓)
  there : ∀ {i} → {x x' : Nbh {i} ⊠ Nbh {i}} → ∀ {𝑓} → x ∈ 𝑓 → x ∈ (x' ∷ 𝑓)

_⊆_ : ∀ {i} → (𝑓 𝑓′ : FinFun {i}) → Set
𝑓 ⊆ 𝑓′ = ∀ {x} → (x ∈ 𝑓 → x ∈ 𝑓′)

⊆-refl : ∀ {i} → {𝑓 : FinFun {i}} → 𝑓 ⊆ 𝑓
⊆-refl x∈𝑓 = x∈𝑓

⊆-trans : ∀ {i} → {𝑓 𝑓′ 𝑓″ : FinFun {i}} → 𝑓 ⊆ 𝑓′ → 𝑓′ ⊆ 𝑓″ → 𝑓 ⊆ 𝑓″
⊆-trans 𝑓⊆𝑓′ 𝑓′⊆𝑓″ x∈𝑓 = 𝑓′⊆𝑓″ (𝑓⊆𝑓′ x∈𝑓)

⊆-lemma₁ : ∀ {i} → {𝑓 𝑓′ : FinFun {i}} → ∀ {x} → (x ∷ 𝑓′) ⊆ 𝑓 → (x ∷ ∅) ⊆ 𝑓
⊆-lemma₁ {x = x} x𝑓′⊆𝑓 here = x𝑓′⊆𝑓 here

⊆-lemma₂ : ∀ {i} → {𝑓 𝑓′ : FinFun {i}} → ∀ {x} → (x ∷ 𝑓′) ⊆ 𝑓 → 𝑓′ ⊆ 𝑓
⊆-lemma₂ x𝑓′⊆𝑓 y∈𝑓′ = x𝑓′⊆𝑓 (there y∈𝑓′)

⊆-lemma₃ : ∀ {i} → {𝑓 : FinFun {i}} → ∀ {x} → 𝑓 ⊆ (x ∷ 𝑓)
⊆-lemma₃ y∈𝑓 = ⊆-lemma₂ ⊆-refl y∈𝑓

⊆-lemma₄ : ∀ {i} → {𝑓 𝑓′ : FinFun {i}} → ∀ {x} → x ∈ 𝑓 → 𝑓′ ⊆ 𝑓 → (x ∷ 𝑓′) ⊆ 𝑓
⊆-lemma₄ x∈𝑓 _ here = x∈𝑓
⊆-lemma₄ x∈𝑓 𝑓′⊆𝑓 (there y∈𝑓) = 𝑓′⊆𝑓 y∈𝑓

⊆-lemma₅ : ∀ {i} → {𝑓 : FinFun {i}} → ∀ {x} → x ∈ 𝑓 → (x ∷ ∅) ⊆ 𝑓
⊆-lemma₅ x∈𝑓 here = x∈𝑓

-- The empty set is a subset of any set.
∅-isSubset : ∀ {i} → {𝑓 : FinFun {i}} → ∅ ⊆ 𝑓
∅-isSubset ()

∪-lemma₁ : ∀ {i} → {𝑓 𝑓′ 𝑓″ : FinFun {i}} → 𝑓 ⊆ 𝑓″ → 𝑓′ ⊆ 𝑓″ → (𝑓 ∪ 𝑓′) ⊆ 𝑓″
∪-lemma₁ {𝑓 = ∅} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ y∈𝑓∪𝑓′ = 𝑓′⊆𝑓″ y∈𝑓∪𝑓′
∪-lemma₁ {𝑓 = x ∷ _} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ here = 𝑓⊆𝑓″ here
∪-lemma₁ {𝑓 = x ∷ 𝑓‴} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ (there y∈𝑓∪𝑓′)
  = ∪-lemma₁ (⊆-trans ⊆-lemma₃ 𝑓⊆𝑓″) 𝑓′⊆𝑓″ y∈𝑓∪𝑓′

∪-lemma₂ : ∀ {i} → {𝑓 𝑓′ : FinFun {i}} → ∀ {x} → x ∈ (𝑓 ∪ 𝑓′) → (x ∈ 𝑓) ∨ (x ∈ 𝑓′)
∪-lemma₂ {𝑓 = ∅} here = inr here
∪-lemma₂ {𝑓 = ∅} (there x∈xs) = inr (there x∈xs)
∪-lemma₂ {𝑓 = x ∷ _} here = inl here
∪-lemma₂ {𝑓 = x ∷ 𝑓″} (there y∈∪) with (∪-lemma₂ y∈∪)
∪-lemma₂ (there y∈∪) | inl y∈𝑓″ = inl (there y∈𝑓″)
∪-lemma₂ (there y∈∪) | inr y∈𝑓′ = inr y∈𝑓′

∪-lemma₃ : ∀ {i} → {𝑓 𝑓′ : FinFun {i}} → 𝑓 ⊆ (𝑓 ∪ 𝑓′)
∪-lemma₃ {𝑓 = x ∷ 𝑓″} here = here
∪-lemma₃ {𝑓 = x ∷ 𝑓″} {x = y} (there y∈𝑓″) = ⊆-lemma₃ y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪-lemma₃ y∈𝑓″

∪-lemma₄ : ∀ {i} → {𝑓 𝑓′ : FinFun {i}} → 𝑓′ ⊆ (𝑓 ∪ 𝑓′)
∪-lemma₄ {𝑓 = ∅} x∈𝑓′ = x∈𝑓′
∪-lemma₄ {𝑓 = x ∷ 𝑓″} {x = y} y∈𝑓′ = ⊆-lemma₃ y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪-lemma₄ y∈𝑓′

∪-lemma₅ : ∀ {i} → {𝑓 𝑓′ 𝑓″ 𝑓‴ : FinFun {i}} → 𝑓 ⊆ 𝑓″ → 𝑓′ ⊆ 𝑓‴ → (𝑓 ∪ 𝑓′) ⊆ (𝑓″ ∪ 𝑓‴)
∪-lemma₅  _ _ x∈𝑓∪𝑓′ with (∪-lemma₂ x∈𝑓∪𝑓′)
∪-lemma₅ {𝑓″ = 𝑓″} {𝑓‴ = 𝑓‴} 𝑓⊆𝑓″ _ x∈𝑓∪𝑓′ | inl x∈𝑓
  = ∪-lemma₃ (𝑓⊆𝑓″ x∈𝑓)
∪-lemma₅ _ 𝑓′⊆𝑓‴ x∈𝑓∪𝑓′ | inr x∈𝑓′
  = ∪-lemma₄ (𝑓′⊆𝑓‴ x∈𝑓′)

∪-lemma₆ : ∀ {i} → {𝑓 𝑓′ : FinFun {i}} → (𝑓 ∪ 𝑓′) ⊆ (𝑓′ ∪ 𝑓)
∪-lemma₆ {𝑓 = 𝑓} x∈𝑓∪𝑓′ with (∪-lemma₂ {𝑓 = 𝑓} x∈𝑓∪𝑓′)
... | inl xy∈𝑓 = ∪-lemma₄ xy∈𝑓
... | inr xy∈𝑓′ = ∪-lemma₃ xy∈𝑓′

∪-lemma₇ : ∀ {i} → {𝑓 𝑓′ 𝑓″ : FinFun {i}} → 𝑓′ ⊆ 𝑓″ → (𝑓 ∪ 𝑓′) ⊆ (𝑓 ∪ 𝑓″)
∪-lemma₇ {𝑓 = 𝑓} 𝑓′⊆𝑓″ x∈𝑓∪𝑓′ with (∪-lemma₂ {𝑓 = 𝑓} x∈𝑓∪𝑓′)
... | inl x∈𝑓 = ∪-lemma₃ x∈𝑓
... | inr x∈𝑓′ = ∪-lemma₄ (𝑓′⊆𝑓″ x∈𝑓′)

∪-lemma₈ : ∀ {i} → {𝑓 𝑓′ 𝑓″ : FinFun {i}} → ((𝑓 ∪ 𝑓′) ∪ 𝑓″) ⊆ (𝑓 ∪ (𝑓′ ∪ 𝑓″))
∪-lemma₈ {𝑓 = 𝑓} {𝑓′} {𝑓″} x∈∪ with (∪-lemma₂ {𝑓 = 𝑓 ∪ 𝑓′} x∈∪)
∪-lemma₈ {𝑓 = 𝑓} _ | inl x∈𝑓∪𝑓′ with (∪-lemma₂ {𝑓 = 𝑓} x∈𝑓∪𝑓′)
∪-lemma₈ {𝑓 = 𝑓} _ | inl _ | inl x∈𝑓 = ∪-lemma₃ {𝑓 = 𝑓} x∈𝑓
∪-lemma₈ {𝑓 = 𝑓} {𝑓′} {𝑓″} _ | inl _ | inr x∈𝑓′ =
  ∪-lemma₄ {𝑓 = 𝑓} (∪-lemma₃ {𝑓 = 𝑓′} x∈𝑓′)
∪-lemma₈ {𝑓 = 𝑓} {𝑓′} _ | inr x∈𝑓″
  = ∪-lemma₄ {𝑓 = 𝑓} (∪-lemma₄ {𝑓 = 𝑓′} x∈𝑓″)

-- From a proof that a pair of neighborhoods is in the
-- empty set, anything.
xy∈∅-abs : ∀ {i} → {p : Set} → {x y : Nbh {i}} →
           (x , y) ∈ ∅ → p
xy∈∅-abs ()
