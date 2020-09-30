{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Valuation.AxiomProofs where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation

Con-⊔ᵥ : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑧 → ⊑ᵥ Γ 𝑦 𝑧 → ValCon Γ 𝑥 𝑦
Con-⊔ᵥ ⊑ᵥ-nil ⊑ᵥ-nil = con-nil
Con-⊔ᵥ {Γ = 𝐴 :: Γ} {𝑥 = ⟪ x , 𝑥 ⟫} {⟪ y , 𝑦 ⟫} {⟪ z , 𝑧 ⟫}
  (⊑ᵥ-cons _ _ _ x⊑z 𝑥⊑𝑧) (⊑ᵥ-cons _ _ _ y⊑z 𝑦⊑𝑧)
  = con-tup conxy con𝑥𝑦
  where conxy = NbhSys.Con-⊔ 𝐴 x⊑z y⊑z
        con𝑥𝑦 = Con-⊔ᵥ 𝑥⊑𝑧 𝑦⊑𝑧

⊑ᵥ-refl : ∀ {𝑥} → ⊑ᵥ Γ 𝑥 𝑥
⊑ᵥ-refl {𝑥 = ⟪⟫}= ⊑ᵥ-nil
⊑ᵥ-refl {Γ = 𝐴 :: Γ} {𝑥 = ⟪ x , 𝑥 ⟫}
  = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ x , 𝑥 ⟫ ⟪ x , 𝑥 ⟫
    (NbhSys.⊑-refl 𝐴) ⊑ᵥ-refl

⊑ᵥ-trans : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 → ⊑ᵥ Γ 𝑦 𝑧 → ⊑ᵥ Γ 𝑥 𝑧
⊑ᵥ-trans {𝑥 = ⟪⟫} {⟪⟫} {⟪⟫} _ _ = ⊑ᵥ-nil
⊑ᵥ-trans {Γ = 𝐴 :: Γ} {𝑥 = ⟪ x , 𝑥 ⟫}
  {⟪ y , 𝑦 ⟫} {⟪ z , 𝑧 ⟫}
  (⊑ᵥ-cons _ _ _ x⊑y 𝑥⊑𝑦)
  (⊑ᵥ-cons _ _ _ y⊑z 𝑦⊑𝑧)
  = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ x , 𝑥 ⟫ ⟪ z , 𝑧 ⟫
    (NbhSys.⊑-trans 𝐴 x⊑y y⊑z) (⊑ᵥ-trans 𝑥⊑𝑦 𝑦⊑𝑧)

⊑ᵥ-⊥ : ∀ {𝑥} → ⊑ᵥ Γ ⊥ᵥ 𝑥
⊑ᵥ-⊥ {𝑥 = ⟪⟫} = ⊑ᵥ-nil
⊑ᵥ-⊥ {Γ = 𝐴 :: Γ} {𝑥 = ⟪ x , 𝑥 ⟫}
  = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ NbhSys.⊥ 𝐴 , ⊥ᵥ ⟫ ⟪ x , 𝑥 ⟫
    (NbhSys.⊑-⊥ 𝐴) (⊑ᵥ-⊥)

⊑ᵥ-⊔ : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑦 𝑥 → ⊑ᵥ Γ 𝑧 𝑥 → (con : ValCon Γ 𝑦 𝑧) →
       ⊑ᵥ Γ (𝑦 ⊔ᵥ 𝑧 [ con ]) 𝑥
⊑ᵥ-⊔ {𝑥 = ⟪⟫} {⟪⟫} {⟪⟫} _ _ _ = ⊑ᵥ-nil
⊑ᵥ-⊔ {Γ = 𝐴 :: Γ} {𝑥 = ⟪ x , 𝑥 ⟫} {⟪ y , 𝑦 ⟫} {⟪ z , 𝑧 ⟫}
  (⊑ᵥ-cons _ _ _ y⊑x 𝑦⊑𝑥) (⊑ᵥ-cons _ _ _ z⊑x 𝑧⊑𝑥)
  (con-tup conyz con𝑦𝑧) =
  ⊑ᵥ-cons (𝐴 :: Γ) (⟪ y , 𝑦 ⟫ ⊔ᵥ ⟪ z , 𝑧 ⟫
  [ con-tup conyz con𝑦𝑧 ]) ⟪ x , 𝑥 ⟫
  y⊔z⊑x (⊑ᵥ-⊔ 𝑦⊑𝑥 𝑧⊑𝑥 con𝑦𝑧)
  where y⊔z⊑x = NbhSys.⊑-⊔ 𝐴 y⊑x z⊑x conyz

⊑ᵥ-⊔-fst : ∀ {𝑥 𝑦} → (con : ValCon Γ 𝑥 𝑦) → ⊑ᵥ Γ 𝑥 (𝑥 ⊔ᵥ 𝑦 [ con ])
⊑ᵥ-⊔-fst {𝑥 = ⟪⟫} {⟪⟫} _ = ⊑ᵥ-nil
⊑ᵥ-⊔-fst {Γ = 𝐴 :: Γ} {𝑥 = ⟪ x , 𝑥 ⟫} {⟪ y , 𝑦 ⟫}
  (con-tup conxy con𝑥𝑦)
  = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ x , 𝑥 ⟫ (⟪ x , 𝑥 ⟫ ⊔ᵥ ⟪ y , 𝑦 ⟫
    [ con-tup conxy con𝑥𝑦 ])
    (NbhSys.⊑-⊔-fst 𝐴 conxy) (⊑ᵥ-⊔-fst con𝑥𝑦)

⊑ᵥ-⊔-snd : ∀ {𝑥 𝑦} →  (con : ValCon Γ 𝑥 𝑦) → ⊑ᵥ Γ 𝑦 (𝑥 ⊔ᵥ 𝑦 [ con ])
⊑ᵥ-⊔-snd {𝑥 = ⟪⟫} {⟪⟫} _ = ⊑ᵥ-nil
⊑ᵥ-⊔-snd {Γ = 𝐴 :: Γ} {𝑥 = ⟪ x , 𝑥 ⟫} {⟪ y , 𝑦 ⟫}
  (con-tup conxy con𝑥𝑦)
  = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ y , 𝑦 ⟫ (⟪ x , 𝑥 ⟫ ⊔ᵥ ⟪ y , 𝑦 ⟫
    [ con-tup conxy con𝑥𝑦 ])
    (NbhSys.⊑-⊔-snd 𝐴 conxy) (⊑ᵥ-⊔-snd con𝑥𝑦)
