{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.beta (𝐴 𝐵 : Ty) where

open import Appmap.Equivalence
open import Base.FinFun
open import Base.Variables hiding (𝐴 ; 𝐵)
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Identity.Instance
open import Scwf.DomainScwf.Appmap.Identity.Relation
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.lam.Instance
open import Scwf.DomainScwf.ArrowStructure.lam.Lemmata 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.PrePost 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation

β-lemma₁ : {𝑡 : tAppmap Γ [ 𝐴 ]} →
           {𝑢 : tAppmap (𝐴 :: Γ) [ 𝐵 ]} → ∀ 𝑥 𝑦 →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ 𝑦 →
           [ 𝑢 ∘ ⟨ idMap Γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦
β-lemma₁ {Γ = Γ} {𝑡} {𝑢} 𝑥 ⟪ y , ⟪⟫ ⟫ (ap↦-intro₁ p)
  = ∘↦-intro 𝑥 ⊥ᵥ ⟪ y ⟫ ⟨⟩𝑥↦⊥ 𝑢⊥↦y
  where id𝑥↦⊥ = Appmap.↦-bottom (idMap Γ)
        𝑡𝑥↦⊥ = Appmap.↦-bottom 𝑡
        ⟨⟩𝑥↦⊥ = ⟨⟩↦-intro 𝑥 ⊥ᵥ id𝑥↦⊥ 𝑡𝑥↦⊥
        tupy⊑⊥ = ⊑ᵥ-cons [ 𝐵 ] ⟪ y ⟫ ⊥ᵥ p ⊑ᵥ-nil
        𝑢⊥↦⊥ = Appmap.↦-bottom 𝑢
        𝑢⊥↦y = Appmap.↦-↓closed 𝑢 tupy⊑⊥ 𝑢⊥↦⊥
β-lemma₁ _ _ (ap↦-intro₂ x y _ _ _ (⊑ₑ-intro₂ _ _ p))
  with (p x y here)
β-lemma₁ {Γ = Γ} {𝑢 = 𝑢} 𝑥 _
  (ap↦-intro₂ x y 𝑓 lam𝑢𝑥↦𝑓 𝑡𝑥↦x _)
  | record { sub = sub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = ∘↦-intro 𝑥 ⟪ x , 𝑥 ⟫ ⟪ y ⟫
    (⟨⟩↦-intro 𝑥 ⟪ x , 𝑥 ⟫ id𝑥↦𝑥 𝑡𝑥↦x) 𝑢x𝑥↦y
  where id𝑥↦𝑥 = id↦-intro 𝑥 𝑥 (NbhSys.⊑-refl (ValNbhSys _))
        y⊑post' = ⊑ᵥ-cons [ 𝐵 ] ⟪ y ⟫ ⟪ post sub ⟫
                  y⊑post ⊑ᵥ-nil
        pre𝑥⊑x𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ pre sub , 𝑥 ⟫
                  ⟪ x , 𝑥 ⟫ pre⊑x
                  (NbhSys.⊑-refl (ValNbhSys _))
        𝑢pre𝑥↦post𝑥 = ↓closedLemma 𝑢 (shrinkLam {Γ = Γ} 𝑢
                      sub⊆𝑓 lam𝑢𝑥↦𝑓)
        𝑢x𝑥↦post = Appmap.↦-mono 𝑢 pre𝑥⊑x𝑥 𝑢pre𝑥↦post𝑥
        𝑢x𝑥↦y = Appmap.↦-↓closed 𝑢 y⊑post' 𝑢x𝑥↦post

β-lemma₂' : {𝑢 : tAppmap (𝐴 :: Γ) [ 𝐵 ]} → ∀ 𝑥 x′ y′ →
            [ 𝑢 ] ⟪ x′ , 𝑥 ⟫ ↦ ⟪ y′ ⟫ →
            ∀ x y → < x , y > ∈ (< x′ , y′ > ∷ ∅) →
            [ 𝑢 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
β-lemma₂' _ _ _ 𝑢x′𝑥↦y′ _ _ here = 𝑢x′𝑥↦y′

β-lemma₂ : {𝑡 : tAppmap Γ [ 𝐴 ]} →
           {𝑢 : tAppmap (𝐴 :: Γ) [ 𝐵 ]} →
           ∀ 𝑥 𝑦 → [ 𝑢 ∘ ⟨ idMap Γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦 →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ 𝑦
β-lemma₂ {Γ = Γ} {𝑢 = 𝑢} 𝑥 ⟪ y , ⟪⟫ ⟫
  (∘↦-intro _ ⟪ x , 𝑥′ ⟫ _
  (⟨⟩↦-intro _ _ (id↦-intro _ _ 𝑥′⊑𝑥) 𝑡𝑥↦x) 𝑢x𝑥′↦y)
  = ap↦-intro₂ x y (< x , y > ∷ ∅) lam𝑥↦xy 𝑡𝑥↦x xy⊑xy
  where xy⊑xy = NbhSys.⊑-refl (ArrNbhSys 𝐴 𝐵)
        x𝑥′⊑x𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ x , 𝑥′ ⟫ ⟪ x , 𝑥 ⟫
                 (NbhSys.⊑-refl 𝐴) 𝑥′⊑𝑥
        𝑢x𝑥↦y = Appmap.↦-mono 𝑢 x𝑥′⊑x𝑥 𝑢x𝑥′↦y
        lam𝑥↦xy = lam↦-intro₂ 𝑥 (< x , y > ∷ ∅)
                  (β-lemma₂' {𝑢 = 𝑢} 𝑥 x y 𝑢x𝑥↦y)

β-equal : {𝑡 : tAppmap Γ [ 𝐴 ]} →
          {𝑢 : tAppmap (𝐴 :: Γ) [ 𝐵 ]} →
          ap (lam 𝑢) 𝑡 ≈ (𝑢 ∘ ⟨ idMap Γ , 𝑡 ⟩)
β-equal = ≈-intro (≼-intro β-lemma₁) (≼-intro β-lemma₂)
