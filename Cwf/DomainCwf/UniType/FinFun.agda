{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.FinFun where

open import Base.Core
open import Cwf.DomainCwf.UniType.Definition

open import Agda.Builtin.Equality

data _∈_ : Nbh ⊠ Nbh → FinFun → Set where
  here : ∀ {x 𝑓} → x ∈ (x ∷ 𝑓)
  there : ∀ {x x' 𝑓} → x ∈ 𝑓 → x ∈ (x' ∷ 𝑓)

_⊆_ : (𝑓 𝑓′ : FinFun) → Set
𝑓 ⊆ 𝑓′ = ∀ {x} → (x ∈ 𝑓 → x ∈ 𝑓′)

⊆-refl : ∀ {𝑓} → 𝑓 ⊆ 𝑓
⊆-refl x∈𝑓 = x∈𝑓

⊆-trans : ∀ {𝑓 𝑓′ 𝑓″} → 𝑓 ⊆ 𝑓′ → 𝑓′ ⊆ 𝑓″ → 𝑓 ⊆ 𝑓″
⊆-trans 𝑓⊆𝑓′ 𝑓′⊆𝑓″ x∈𝑓 = 𝑓′⊆𝑓″ (𝑓⊆𝑓′ x∈𝑓)

⊆-lemma₁ : ∀ {𝑓 𝑓′ x} → (x ∷ 𝑓′) ⊆ 𝑓 → (x ∷ ∅) ⊆ 𝑓
⊆-lemma₁ {x = x} x𝑓′⊆𝑓 here = x𝑓′⊆𝑓 here

⊆-lemma₂ : ∀ {𝑓 𝑓′ x} → (x ∷ 𝑓′) ⊆ 𝑓 → 𝑓′ ⊆ 𝑓
⊆-lemma₂ x𝑓′⊆𝑓 y∈𝑓′ = x𝑓′⊆𝑓 (there y∈𝑓′)

⊆-lemma₃ : ∀ {𝑓 x} → 𝑓 ⊆ (x ∷ 𝑓)
⊆-lemma₃ y∈𝑓 = ⊆-lemma₂ ⊆-refl y∈𝑓

⊆-lemma₄ : ∀ {𝑓 𝑓′ x} → x ∈ 𝑓 → 𝑓′ ⊆ 𝑓 → (x ∷ 𝑓′) ⊆ 𝑓
⊆-lemma₄ x∈𝑓 _ here = x∈𝑓
⊆-lemma₄ x∈𝑓 𝑓′⊆𝑓 (there y∈𝑓) = 𝑓′⊆𝑓 y∈𝑓

⊆-lemma₅ : ∀ {𝑓 x} → x ∈ 𝑓 → (x ∷ ∅) ⊆ 𝑓
⊆-lemma₅ x∈𝑓 here = x∈𝑓

⊆-lemma₆ : ∀ {𝑓 x y} → (x ∷ 𝑓) ⊆ (x ∷ (y ∷ 𝑓))
⊆-lemma₆ here = here
⊆-lemma₆ (there x∈𝑓) = there (there x∈𝑓)

-- The empty set is a subset of any set.
∅-isSubset : ∀ {𝑓} → ∅ ⊆ 𝑓
∅-isSubset ()

∪-lemma₁ : ∀ {𝑓 𝑓′ 𝑓″} → 𝑓 ⊆ 𝑓″ → 𝑓′ ⊆ 𝑓″ → (𝑓 ∪ 𝑓′) ⊆ 𝑓″
∪-lemma₁ {𝑓 = ∅} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ y∈𝑓∪𝑓′ = 𝑓′⊆𝑓″ y∈𝑓∪𝑓′
∪-lemma₁ {𝑓 = x ∷ _} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ here = 𝑓⊆𝑓″ here
∪-lemma₁ {𝑓 = x ∷ 𝑓‴} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ (there y∈𝑓∪𝑓′)
  = ∪-lemma₁ (⊆-trans ⊆-lemma₃ 𝑓⊆𝑓″) 𝑓′⊆𝑓″ y∈𝑓∪𝑓′

∪-lemma₂ : ∀ {𝑓 𝑓′ x} → x ∈ (𝑓 ∪ 𝑓′) → (x ∈ 𝑓) ∨ (x ∈ 𝑓′)
∪-lemma₂ {𝑓 = ∅} here = inr here
∪-lemma₂ {𝑓 = ∅} (there x∈xs) = inr (there x∈xs)
∪-lemma₂ {𝑓 = x ∷ _} here = inl here
∪-lemma₂ {𝑓 = x ∷ 𝑓″} (there y∈∪) with (∪-lemma₂ y∈∪)
∪-lemma₂ (there y∈∪) | inl y∈𝑓″ = inl (there y∈𝑓″)
∪-lemma₂ (there y∈∪) | inr y∈𝑓′ = inr y∈𝑓′

∪-lemma₃ : ∀ {𝑓 𝑓′} → 𝑓 ⊆ (𝑓 ∪ 𝑓′)
∪-lemma₃ {𝑓 = x ∷ 𝑓″} here = here
∪-lemma₃ {𝑓 = x ∷ 𝑓″} {x = y} (there y∈𝑓″) = ⊆-lemma₃ y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪-lemma₃ y∈𝑓″

∪-lemma₄ : ∀ {𝑓 𝑓′} → 𝑓′ ⊆ (𝑓 ∪ 𝑓′)
∪-lemma₄ {𝑓 = ∅} x∈𝑓′ = x∈𝑓′
∪-lemma₄ {𝑓 = x ∷ 𝑓″} {x = y} y∈𝑓′ = ⊆-lemma₃ y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪-lemma₄ y∈𝑓′

∪-lemma₅ : ∀ {𝑓 𝑓′ 𝑓″ 𝑓‴} → 𝑓 ⊆ 𝑓″ → 𝑓′ ⊆ 𝑓‴ → (𝑓 ∪ 𝑓′) ⊆ (𝑓″ ∪ 𝑓‴)
∪-lemma₅  _ _ x∈𝑓∪𝑓′ with (∪-lemma₂ x∈𝑓∪𝑓′)
∪-lemma₅ {𝑓″ = 𝑓″} {𝑓‴ = 𝑓‴} 𝑓⊆𝑓″ _ x∈𝑓∪𝑓′ | inl x∈𝑓
  = ∪-lemma₃ (𝑓⊆𝑓″ x∈𝑓)
∪-lemma₅ _ 𝑓′⊆𝑓‴ x∈𝑓∪𝑓′ | inr x∈𝑓′
  = ∪-lemma₄ (𝑓′⊆𝑓‴ x∈𝑓′)

∪-lemma₆ : ∀ {𝑓 𝑓′} → (𝑓 ∪ 𝑓′) ⊆ (𝑓′ ∪ 𝑓)
∪-lemma₆ {𝑓 = 𝑓} x∈𝑓∪𝑓′ with (∪-lemma₂ {𝑓 = 𝑓} x∈𝑓∪𝑓′)
... | inl xy∈𝑓 = ∪-lemma₄ xy∈𝑓
... | inr xy∈𝑓′ = ∪-lemma₃ xy∈𝑓′

∪-lemma₇ : ∀ {𝑓 𝑓′ 𝑓″} → 𝑓′ ⊆ 𝑓″ → (𝑓 ∪ 𝑓′) ⊆ (𝑓 ∪ 𝑓″)
∪-lemma₇ {𝑓 = 𝑓} 𝑓′⊆𝑓″ x∈𝑓∪𝑓′ with (∪-lemma₂ {𝑓 = 𝑓} x∈𝑓∪𝑓′)
... | inl x∈𝑓 = ∪-lemma₃ x∈𝑓
... | inr x∈𝑓′ = ∪-lemma₄ (𝑓′⊆𝑓″ x∈𝑓′)

∪-lemma₈ : ∀ {𝑓 𝑓′ 𝑓″} → ((𝑓 ∪ 𝑓′) ∪ 𝑓″) ⊆ (𝑓 ∪ (𝑓′ ∪ 𝑓″))
∪-lemma₈ {𝑓 = 𝑓} {𝑓′} {𝑓″} x∈∪ with (∪-lemma₂ {𝑓 = 𝑓 ∪ 𝑓′} x∈∪)
∪-lemma₈ {𝑓 = 𝑓} _ | inl x∈𝑓∪𝑓′ with (∪-lemma₂ {𝑓 = 𝑓} x∈𝑓∪𝑓′)
∪-lemma₈ {𝑓 = 𝑓} _ | inl _ | inl x∈𝑓 = ∪-lemma₃ {𝑓 = 𝑓} x∈𝑓
∪-lemma₈ {𝑓 = 𝑓} {𝑓′} {𝑓″} _ | inl _ | inr x∈𝑓′ =
  ∪-lemma₄ {𝑓 = 𝑓} (∪-lemma₃ {𝑓 = 𝑓′} x∈𝑓′)
∪-lemma₈ {𝑓 = 𝑓} {𝑓′} _ | inr x∈𝑓″
  = ∪-lemma₄ {𝑓 = 𝑓} (∪-lemma₄ {𝑓 = 𝑓′} x∈𝑓″)

∪-assoc : ∀ {f g h} → (f ∪ (g ∪ h)) ≡ ((f ∪ g) ∪ h)
∪-assoc {f = ∅} {g} {h} = refl
∪-assoc {f = _ ∷ f} {g} {h} rewrite (∪-assoc {f = f} {g} {h}) = refl

-- From a proof that a pair of neighborhoods is in the
-- empty set, anything.
xy∈∅-abs : {p : Set} → ∀ {x y} → (x , y) ∈ ∅ → p
xy∈∅-abs ()
