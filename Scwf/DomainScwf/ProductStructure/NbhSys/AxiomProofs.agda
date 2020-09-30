{-# OPTIONS --safe #-}

open import NbhSys.Definition

module Scwf.DomainScwf.ProductStructure.NbhSys.AxiomProofs
  (𝒟 𝒟′ : NbhSys) where

open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition 𝒟 𝒟′
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation 𝒟 𝒟′

private
  variable
    x y z : ProdNbh

Con-⊔ₓ : x ⊑ₓ z → y ⊑ₓ z → ProdCon x y
Con-⊔ₓ {⊥ₓ} {⊥ₓ}_ _ = conₓ-⊥₂
Con-⊔ₓ {⊥ₓ} {< y₁ , y₂ >}_ _ = conₓ-⊥₂
Con-⊔ₓ {< x₁ , x₂ >} {y = ⊥ₓ} _ _ = conₓ-⊥₁
Con-⊔ₓ {< x₁ , x₂ >} {< z₁ , z₂ >} {< y₁ , y₂ >}
  (⊑ₓ-intro₂ x₁⊑z₁ x₂⊑z₂) (⊑ₓ-intro₂ y₁⊑z₁ y₂⊑z₂)
  = con-pair (NbhSys.Con-⊔ 𝒟 x₁⊑z₁ y₁⊑z₁) (NbhSys.Con-⊔ 𝒟′ x₂⊑z₂ y₂⊑z₂)

⊑ₓ-refl : x ⊑ₓ x
⊑ₓ-refl {x = ⊥ₓ} = ⊑ₓ-intro₁
⊑ₓ-refl {x = < x₁ , x₂ >}
  = ⊑ₓ-intro₂ (NbhSys.⊑-refl 𝒟) (NbhSys.⊑-refl 𝒟′)

⊑ₓ-trans : x ⊑ₓ y → y ⊑ₓ z → x ⊑ₓ z
⊑ₓ-trans {z = z} ⊑ₓ-intro₁ ⊑ₓ-intro₁ = ⊑ₓ-intro₁
⊑ₓ-trans ⊑ₓ-intro₁ (⊑ₓ-intro₂ _ _) = ⊑ₓ-intro₁
⊑ₓ-trans (⊑ₓ-intro₂ x₁⊑y₁ x₂⊑y₂)
  (⊑ₓ-intro₂ y₁⊑z₁ y₂⊑z₂)
  = ⊑ₓ-intro₂ (NbhSys.⊑-trans 𝒟 x₁⊑y₁ y₁⊑z₁)
    (NbhSys.⊑-trans 𝒟′ x₂⊑y₂ y₂⊑z₂)

⊑ₓ-⊥ : ⊥ₓ ⊑ₓ x
⊑ₓ-⊥ {x = x} = ⊑ₓ-intro₁

⊑ₓ-⊔ : y ⊑ₓ x → z ⊑ₓ x → (con : ProdCon y z) → (y ⊔ₓ z [ con ]) ⊑ₓ x
⊑ₓ-⊔ {⊥ₓ} {x} {< z₁ , z₂ >} _ z⊑x _ = z⊑x
⊑ₓ-⊔ {⊥ₓ} {x} {⊥ₓ} _ _ - = ⊑ₓ-intro₁
⊑ₓ-⊔ {< y₁ , y₂ >} {x} {⊥ₓ} y⊑x _ - = y⊑x
⊑ₓ-⊔ {< y₁ , y₂ >} {x} {< z₁ , z₂ >}
  (⊑ₓ-intro₂ y₁⊑w₁ y₂⊑w₂)
  (⊑ₓ-intro₂ z₁⊑w₁ z₂⊑w₂) (con-pair cony₁z₁ cony₂z₂)
  = ⊑ₓ-intro₂ y₁⊔z₁⊑w₁ y₂⊔z₂⊑w₂
  where y₁⊔z₁⊑w₁ = NbhSys.⊑-⊔ 𝒟 y₁⊑w₁ z₁⊑w₁ cony₁z₁
        y₂⊔z₂⊑w₂ = NbhSys.⊑-⊔ 𝒟′ y₂⊑w₂ z₂⊑w₂ cony₂z₂

⊑ₓ-⊔-fst : (con : ProdCon x y) → x ⊑ₓ (x ⊔ₓ y [ con ])
⊑ₓ-⊔-fst {⊥ₓ} {_} _ = ⊑ₓ-intro₁
⊑ₓ-⊔-fst {< x₁ , y₁ >} {⊥ₓ} _ =
  ⊑ₓ-intro₂ (NbhSys.⊑-refl 𝒟) ((NbhSys.⊑-refl 𝒟′))
⊑ₓ-⊔-fst {< x₁ , y₁ >} {< x₂ , y₂ >} (con-pair conx₁x₂ cony₁y₂) =
  ⊑ₓ-intro₂ x₁⊑x₁⊔x₂ y₁⊑y₁⊔y₂
  where x₁⊑x₁⊔x₂ = NbhSys.⊑-⊔-fst 𝒟 conx₁x₂
        y₁⊑y₁⊔y₂ = NbhSys.⊑-⊔-fst 𝒟′ cony₁y₂

⊑ₓ-⊔-snd : (con : ProdCon x y) → y ⊑ₓ (x ⊔ₓ y [ con ])
⊑ₓ-⊔-snd {y = ⊥ₓ} _ = ⊑ₓ-intro₁
⊑ₓ-⊔-snd {⊥ₓ} {< x₂ , y₂ >} _ =
  ⊑ₓ-intro₂ (NbhSys.⊑-refl 𝒟) ((NbhSys.⊑-refl 𝒟′))
⊑ₓ-⊔-snd {< x₁ , y₁ >} {< x₂ , y₂ >} (con-pair conx₁x₂ cony₁y₂) =
  ⊑ₓ-intro₂ x₂⊑x₁⊔x₂ y₂⊑y₁⊔y₂
  where x₂⊑x₁⊔x₂ = NbhSys.⊑-⊔-snd 𝒟 conx₁x₂
        y₂⊑y₁⊔y₂ = NbhSys.⊑-⊔-snd 𝒟′ cony₁y₂
