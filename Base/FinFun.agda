{-# OPTIONS --safe #-}

module Base.FinFun where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition

open import Agda.Primitive

-- Finite functions are lists of pairs.
data FinFun (A B : Set) : Set where
  ∅ : FinFun A B
  _∷_ : A ⊠ B → FinFun A B → FinFun A B

private
  variable
    𝑓 𝑓′ 𝑓″ 𝑓‴ : FinFun A B

-- Short-hand when dealing with neighborhood systems.
NbhFinFun : Ty → Ty → Set
NbhFinFun 𝐴 𝐵 = FinFun (NbhSys.Nbh 𝐴) (NbhSys.Nbh 𝐵)

-- Set membership relation.
data _∈_ {A B : Set} : A ⊠ B → FinFun A B → Set where
  here : ∀ {x 𝑓} → x ∈ (x ∷ 𝑓)
  there : ∀ {x x' 𝑓} → x ∈ 𝑓 → x ∈ (x' ∷ 𝑓)

-- Subset relation.
_⊆_ : (𝑓 𝑓′ : FinFun A B) → Set
𝑓 ⊆ 𝑓′ = ∀ x → (x ∈ 𝑓 → x ∈ 𝑓′)

⊆-refl : 𝑓 ⊆ 𝑓
⊆-refl x x∈𝑓 = x∈𝑓

⊆-trans : 𝑓 ⊆ 𝑓′ → 𝑓′ ⊆ 𝑓″ → 𝑓 ⊆ 𝑓″
⊆-trans 𝑓⊆𝑓′ 𝑓′⊆𝑓″ x x∈𝑓 = 𝑓′⊆𝑓″ x (𝑓⊆𝑓′ x x∈𝑓)

⊆-lemma₁ : ∀ x → (x ∷ 𝑓′) ⊆ 𝑓 → (x ∷ ∅) ⊆ 𝑓
⊆-lemma₁ x x𝑓′⊆𝑓 _ here = x𝑓′⊆𝑓 x here

⊆-lemma₂ : ∀ x → (x ∷ 𝑓′) ⊆ 𝑓 → 𝑓′ ⊆ 𝑓
⊆-lemma₂ x x𝑓′⊆𝑓 y y∈𝑓′ = x𝑓′⊆𝑓 y (there y∈𝑓′)

⊆-lemma₃ : ∀ x → 𝑓 ⊆ (x ∷ 𝑓)
⊆-lemma₃ x y y∈𝑓 = ⊆-lemma₂ x ⊆-refl y y∈𝑓

⊆-lemma₄ : ∀ x → x ∈ 𝑓 → 𝑓′ ⊆ 𝑓 → (x ∷ 𝑓′) ⊆ 𝑓
⊆-lemma₄ _ x∈𝑓 _ _ here = x∈𝑓
⊆-lemma₄ _ x∈𝑓 𝑓′⊆𝑓 y (there y∈𝑓) = 𝑓′⊆𝑓 y y∈𝑓

-- Set union.
_∪_ : FinFun A B → FinFun A B → FinFun A B
(x ∷ 𝑓) ∪ 𝑓′ = x ∷ (𝑓 ∪ 𝑓′)
∅ ∪ 𝑓′ = 𝑓′

-- The empty set is a subset of any set.
∅-isSubset : ∅ ⊆ 𝑓
∅-isSubset _ ()

∪-lemma₁ : 𝑓 ⊆ 𝑓″ → 𝑓′ ⊆ 𝑓″ → (𝑓 ∪ 𝑓′) ⊆ 𝑓″
∪-lemma₁ {𝑓 = ∅} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ y y∈𝑓∪𝑓′ = 𝑓′⊆𝑓″ y y∈𝑓∪𝑓′
∪-lemma₁ {𝑓 = x ∷ _} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ _ here = 𝑓⊆𝑓″ x here
∪-lemma₁ {𝑓 = x ∷ 𝑓‴} 𝑓⊆𝑓″ 𝑓′⊆𝑓″ y (there y∈𝑓∪𝑓′)
  = ∪-lemma₁ (⊆-trans (⊆-lemma₃ x) 𝑓⊆𝑓″) 𝑓′⊆𝑓″ y y∈𝑓∪𝑓′

∪-lemma₂ : ∀ x → x ∈ (𝑓 ∪ 𝑓′) → (x ∈ 𝑓) ∨ (x ∈ 𝑓′)
∪-lemma₂ {𝑓 = ∅} _ here = inr here
∪-lemma₂ {𝑓 = ∅} _ (there x∈xs) = inr (there x∈xs)
∪-lemma₂ {𝑓 = x ∷ _} _ here = inl here
∪-lemma₂ {𝑓 = x ∷ 𝑓″} y (there y∈∪) with (∪-lemma₂ y y∈∪)
∪-lemma₂ y (there y∈∪) | inl y∈𝑓″ = inl (there y∈𝑓″)
∪-lemma₂ y (there y∈∪) | inr y∈𝑓′ = inr y∈𝑓′

∪-lemma₃ : ∀ x → x ∈ 𝑓 → x ∈ (𝑓 ∪ 𝑓′)
∪-lemma₃ {𝑓 = x ∷ 𝑓″} _ here = here
∪-lemma₃ {𝑓 = x ∷ 𝑓″} y (there y∈𝑓″) = ⊆-lemma₃ x y y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪-lemma₃ y y∈𝑓″

∪-lemma₄ : ∀ x → x ∈ 𝑓′ → x ∈ (𝑓 ∪ 𝑓′)
∪-lemma₄ {𝑓 = ∅} x x∈𝑓′ = x∈𝑓′
∪-lemma₄ {𝑓 = x ∷ 𝑓″} y y∈𝑓′ = ⊆-lemma₃ x y y∈𝑓″∪𝑓′
  where y∈𝑓″∪𝑓′ = ∪-lemma₄ y y∈𝑓′

∪-lemma₅ : 𝑓 ⊆ 𝑓″ → 𝑓′ ⊆ 𝑓‴ → (𝑓 ∪ 𝑓′) ⊆ (𝑓″ ∪ 𝑓‴)
∪-lemma₅  _ _ x x∈𝑓∪𝑓′ with (∪-lemma₂ x x∈𝑓∪𝑓′)
∪-lemma₅ {𝑓″ = 𝑓″} {𝑓‴ = 𝑓‴} 𝑓⊆𝑓″ _ x x∈𝑓∪𝑓′ | inl x∈𝑓
  = ∪-lemma₃ x (𝑓⊆𝑓″ x x∈𝑓)
∪-lemma₅ _ 𝑓′⊆𝑓‴ x x∈𝑓∪𝑓′ | inr x∈𝑓′
  = ∪-lemma₄ x (𝑓′⊆𝑓‴ x x∈𝑓′)

-- From a proof that a pair of neighborhoods is in the
-- empty set, anything.
xy∈∅-abs : {p : Set} → ∀ {x y} →
           _∈_ {A} {B} < x , y > ∅ → p
xy∈∅-abs ()
