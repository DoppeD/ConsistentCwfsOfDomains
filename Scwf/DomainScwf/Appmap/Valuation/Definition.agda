{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Valuation.Definition where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition

-- Valuations of contexts are tuples of appropriately
-- typed neighborhoods.
data Valuation : Ctx n → Set where
  ⟪⟫ : Valuation []
  ⟪_,_⟫ : NbhSys.Nbh 𝐴 → Valuation Γ → Valuation (𝐴 :: Γ)

-- Notation for 1-tuples.
⟪_⟫ : ∀ x → Valuation (𝐴 :: [])
⟪ x ⟫ = ⟪ x , ⟪⟫ ⟫

data ValCon : (Γ : Ctx n) → (𝑥 𝑦 : Valuation Γ) → Set where
  con-nil : ValCon [] ⟪⟫ ⟪⟫
  con-tup : ∀ {Γ : Ctx n} → ∀ {x y 𝑥 𝑦} →
            NbhSys.Con 𝐴 x y → ValCon Γ 𝑥 𝑦 →
            ValCon (𝐴 :: Γ) ⟪ x , 𝑥 ⟫ ⟪ y , 𝑦 ⟫

-- The supremum of valuations is defined component-wise.
_⊔ᵥ_[_] : (𝑥 : Valuation Γ) → (𝑦 : Valuation Γ) → ValCon Γ 𝑥 𝑦 →
          Valuation Γ
_⊔ᵥ_[_] ⟪⟫ ⟪⟫ _ = ⟪⟫
_⊔ᵥ_[_] {Γ = h :: _} ⟪ x , 𝑥 ⟫ ⟪ y , 𝑦 ⟫ (con-tup conxy con𝑥𝑦)
  = ⟪ [ h ] x ⊔ y [ conxy ] , 𝑥 ⊔ᵥ 𝑦 [ con𝑥𝑦 ] ⟫

⊥ᵥ : Valuation Γ
⊥ᵥ {Γ = []} = ⟪⟫
⊥ᵥ {Γ = h :: _} = ⟪ NbhSys.⊥ h , ⊥ᵥ ⟫

-- Analogous to head, but for valuations.
ctHead : Valuation Γ → NbhSys.Nbh (head Γ)
ctHead ⟪ x , _ ⟫ = x

-- Analogous to tail for lists.
ctTail : Valuation Γ → Valuation (tail Γ)
ctTail ⟪ _ , 𝑥 ⟫ = 𝑥

toValCon : ∀ {𝒟 x y} → (conxy : NbhSys.Con 𝒟 x y) →
           ValCon [ 𝒟 ] ⟪ x ⟫ ⟪ y ⟫
toValCon conxy = con-tup conxy con-nil

fromValCon : ∀ {𝒟 x y} → (conxy : ValCon [ 𝒟 ] ⟪ x ⟫ ⟪ y ⟫) →
             NbhSys.Con 𝒟 x y
fromValCon (con-tup conxy _) = conxy
