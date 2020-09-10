{-# OPTIONS --safe #-}

open import NbhSys.Definition

module Scwf.DomainScwf.ProductStructure.NbhSys.Definition
  (𝒟 𝒟′ : NbhSys) where

data ProdNbh : Set where
  ⊥ₓ : ProdNbh
  <_,_> : NbhSys.Nbh 𝒟 → NbhSys.Nbh 𝒟′ → ProdNbh

data ProdCon : ProdNbh → ProdNbh → Set where
  conₓ-⊥₁ : ∀ {x} → ProdCon x ⊥ₓ
  conₓ-⊥₂ : ∀ {x} → ProdCon ⊥ₓ x
  con-pair : ∀ {x₁ x₂ x′₁ x′₂} → NbhSys.Con 𝒟 x₁ x′₁ → NbhSys.Con 𝒟′ x₂ x′₂ →
             ProdCon < x₁ , x₂ > < x′₁ , x′₂ >

_⊔ₓ_[_] : (x : ProdNbh) → (y : ProdNbh) → (con : ProdCon x y) →
       ProdNbh
⊥ₓ ⊔ₓ ⊥ₓ [ _ ] = ⊥ₓ
⊥ₓ ⊔ₓ < x₁ , x₂ > [ _ ] = < x₁ , x₂ >
< x₁ , x₂ > ⊔ₓ ⊥ₓ [ _ ] = < x₁ , x₂ >
< x₁ , x₂ > ⊔ₓ < x′₁ , x′₂ > [ con-pair conx₁x′₁ conx₂x′₂ ]
  = < [ 𝒟 ] x₁ ⊔ x′₁ [ conx₁x′₁ ] , [ 𝒟′ ] x₂ ⊔ x′₂ [ conx₂x′₂ ] >
