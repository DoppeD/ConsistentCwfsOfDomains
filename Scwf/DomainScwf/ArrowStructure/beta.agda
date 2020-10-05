{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.beta (𝐴 𝐵 : Ty) where

open import Appmap.Equivalence
open import Appmap.Composition.Instance
open import Appmap.Composition.Relation
open import Base.FinFun
open import Base.Variables hiding (𝐴 ; 𝐵)
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Identity.Instance
open import Scwf.DomainScwf.Appmap.Identity.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.lam.Instance
open import Scwf.DomainScwf.ArrowStructure.lam.Lemmata 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation

β-lemma₁ : {𝑡 : Term Γ 𝐴} →
           {𝑢 : Term (𝐴 :: Γ) 𝐵} → ∀ {𝑥 y} →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ y →
           [ 𝑢 ∘ ⟨ idMap Γ , 𝑡 ⟩ ] 𝑥 ↦ y
β-lemma₁ {Γ = Γ} {𝑡} {𝑢} (ap↦-intro₁ p)
  = ∘↦-intro ⟨⟩𝑥↦⊥ 𝑢⊥↦y
  where id𝑥↦⊥ = Appmap.↦-bottom (idMap Γ)
        𝑡𝑥↦⊥ = Appmap.↦-bottom 𝑡
        ⟨⟩𝑥↦⊥ = ⟨⟩↦-intro {𝑦 = ⟪ _ ,, ⊥ᵥ ⟫} id𝑥↦⊥ 𝑡𝑥↦⊥
        𝑢⊥↦⊥ = Appmap.↦-bottom 𝑢
        𝑢⊥↦y = Appmap.↦-↓closed 𝑢 p 𝑢⊥↦⊥
β-lemma₁ (ap↦-intro₂ _ _ _ _ (⊑ₑ-intro₂ _ _ p))
  with (p here)
β-lemma₁ {Γ = Γ} {𝑢 = 𝑢}
  (ap↦-intro₂ {x = x} {y} con𝑓 _ lam𝑢𝑥↦𝑓 𝑡𝑥↦x _)
  | record { sub = sub
           ; postablesub = postablesub
           ; preablesub = preablesub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = ∘↦-intro (⟨⟩↦-intro {𝑦 = ⟪ x ,, _ ⟫} id𝑥↦𝑥 𝑡𝑥↦x) 𝑢x𝑥↦y
  where id𝑥↦𝑥 = id↦-intro (NbhSys.⊑-refl (ValNbhSys _))
        pre𝑥⊑x𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) pre⊑x
                  (NbhSys.⊑-refl (ValNbhSys _))
        𝑢pre𝑥↦post𝑥 = ↓closedLemma 𝑢 (subsetIsCon con𝑓 sub⊆𝑓)
                      preablesub postablesub
                      (shrinkLam {Γ = Γ} 𝑢
                      sub⊆𝑓 lam𝑢𝑥↦𝑓)
        𝑢x𝑥↦post = Appmap.↦-mono 𝑢 pre𝑥⊑x𝑥 𝑢pre𝑥↦post𝑥
        𝑢x𝑥↦y = Appmap.↦-↓closed 𝑢 y⊑post 𝑢x𝑥↦post

β-lemma₂' : {𝑢 : Term (𝐴 :: Γ) 𝐵} → ∀ {𝑥 x′ y′} →
            [ 𝑢 ] ⟪ x′ ,, 𝑥 ⟫ ↦ y′ →
            ∀ {x y} → (x , y) ∈ ((x′ , y′) ∷ ∅) →
            [ 𝑢 ] ⟪ x ,, 𝑥 ⟫ ↦ y
β-lemma₂' 𝑢x′𝑥↦y′ here = 𝑢x′𝑥↦y′

β-lemma₂ : {𝑡 : Term Γ 𝐴} →
           {𝑢 : Term (𝐴 :: Γ) 𝐵} →
           ∀ {𝑥 𝑦} → [ 𝑢 ∘ ⟨ idMap Γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦 →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ 𝑦
β-lemma₂ {Γ = Γ} {𝑢 = 𝑢}
  (∘↦-intro (⟨⟩↦-intro (id↦-intro 𝑥′⊑𝑥) 𝑡𝑥↦x) 𝑢x𝑥′↦y)
  = ap↦-intro₂ singletonIsCon singletonIsCon
    lam𝑥↦xy 𝑡𝑥↦x xy⊑xy
  where xy⊑xy = NbhSys.⊑-refl (𝐴 ⇒ 𝐵)
        x𝑥′⊑x𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) (NbhSys.⊑-refl 𝐴) 𝑥′⊑𝑥
        𝑢x𝑥↦y = Appmap.↦-mono 𝑢 x𝑥′⊑x𝑥 𝑢x𝑥′↦y
        lam𝑥↦xy = lam↦-intro₂ singletonIsCon
                  (β-lemma₂' {𝑢 = 𝑢} 𝑢x𝑥↦y)

β-equal : {𝑡 : Term Γ 𝐴} →
          {𝑢 : Term (𝐴 :: Γ) 𝐵} →
          ap (lam 𝑢) 𝑡 ≈ (𝑢 ∘ ⟨ idMap Γ , 𝑡 ⟩)
β-equal = ≈-intro (≼-intro β-lemma₁) (≼-intro β-lemma₂)
