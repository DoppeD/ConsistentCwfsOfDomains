{-# OPTIONS --safe #-}

module Appmap.Definition where

open import NbhSys.Definition

open import Agda.Builtin.Sigma

private
  variable
    𝒟 𝒟′ : NbhSys

record Appmap (𝒟 𝒟′ : NbhSys) : Set₁ where
  field
    -- The mapping itself.
    _↦_ : NbhSys.Nbh 𝒟 → NbhSys.Nbh 𝒟′ → Set

    -- Axioms for the mapping.
    ↦-mono : ∀ {x y z} → [ 𝒟 ] x ⊑ y → x ↦ z → y ↦ z
    ↦-bottom : ∀ {x} → x ↦ NbhSys.⊥ 𝒟′
    ↦-↓closed : ∀ {x y z} → [ 𝒟′ ] y ⊑ z → x ↦ z → x ↦ y
    ↦-↑directed : ∀ {x y z} → x ↦ y → x ↦ z → (con : NbhSys.Con 𝒟′ y z) →
                  x ↦ ([ 𝒟′ ] y ⊔ z [ con ])
    ↦-con : ∀ {x y x′ y′} → x ↦ y → x′ ↦ y′ → NbhSys.Con 𝒟 x x′ →
            NbhSys.Con 𝒟′ y y′

-- Some simplifying syntax.
[_]_↦_ : Appmap 𝒟 𝒟′ → NbhSys.Nbh 𝒟 → NbhSys.Nbh 𝒟′ → Set
[ γ ] x ↦ y = Appmap._↦_ γ x y

-- A (trivial) proof that approximable mappings are total.
↦-total : (γ : Appmap 𝒟 𝒟′) → ∀ {x} →
          Σ (NbhSys.Nbh 𝒟′) λ y → [ γ ] x ↦ y
↦-total {𝒟′ = 𝒟′} γ = NbhSys.⊥ 𝒟′ , Appmap.↦-bottom γ
