{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.beta where

open import Appmap.Equivalence
open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Identity.Instance
open import Scwf.DomainScwf.Appmap.Identity.Relation
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.ap.Instance
open import Ucwf.DomainUcwf.LambdaBeta.ap.Relation
open import Ucwf.DomainUcwf.LambdaBeta.lam.Instance
open import Ucwf.DomainUcwf.LambdaBeta.lam.Lemmata
open import Ucwf.DomainUcwf.LambdaBeta.lam.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.DomainUcwf.UniType.PrePost
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.SizedFinFun

open import Agda.Builtin.Nat

private
  variable
    𝑡 : tAppmap (nToCtx m) [ UniType ]
    𝑢 : tAppmap (nToCtx (suc m)) [ UniType ]

β-lemma₁ : ∀ 𝑥 𝑦 →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ 𝑦 →
           [ 𝑢 ∘ ⟨ idMap (nToCtx m) , 𝑡 ⟩ ] 𝑥 ↦ 𝑦
β-lemma₁ {m = m} {𝑢 = 𝑢} {𝑡 = 𝑡} 𝑥 ⟪ ⊥ᵤ , ⟪⟫ ⟫ _
  = ∘↦-intro 𝑥 ⊥ᵥ ⟪ ⊥ᵤ ⟫ ⟨⟩⊥↦⊥ 𝑢⊥↦⊥
  where id⊥↦⊥ = Appmap.↦-bottom (idMap (nToCtx m))
        𝑡𝑥↦⊥ = Appmap.↦-bottom 𝑡
        ⟨⟩⊥↦⊥ = ⟨⟩↦-intro 𝑥 ⊥ᵥ id⊥↦⊥ 𝑡𝑥↦⊥
        𝑢⊥↦⊥ = Appmap.↦-bottom 𝑢
β-lemma₁ _ ⟪ λᵤ 𝑓 , ⟪⟫ ⟫
  (ap↦-intro₂ x′ _ _ _ _ (⊑ᵤ-intro₂ _ _ p))
  with (p x′ (λᵤ 𝑓) here)
β-lemma₁ {m = m} {𝑢 = 𝑢} {𝑡 = 𝑡} 𝑥 ⟪ λᵤ 𝑓 , ⟪⟫ ⟫
  (ap↦-intro₂ x _ 𝑔 lam𝑢𝑥↦𝑔 𝑡𝑥↦x _)
  | record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = sub⊆𝑓′
           }
  = ∘↦-intro 𝑥 ⟪ x , 𝑥 ⟫ ⟪ λᵤ 𝑓 ⟫
    (⟨⟩↦-intro 𝑥 ⟪ x , 𝑥 ⟫ id𝑥↦𝑥 𝑡𝑥↦x) 𝑢x𝑥↦y
  where id𝑥↦𝑥 = id↦-intro 𝑥 𝑥 (NbhSys.⊑-refl (ValNbhSys _))
        y⊑post' = ⊑ᵥ-cons [ UniType ] ⟪ λᵤ 𝑓 ⟫
                  ⟪ post sub ⟫ y⊑ᵤpost ⊑ᵥ-nil
        pre𝑥⊑x𝑥 = ⊑ᵥ-cons (nToCtx (suc m)) ⟪ pre sub , 𝑥 ⟫
                  ⟪ x , 𝑥 ⟫ pre⊑ᵤx
                  (NbhSys.⊑-refl (ValNbhSys _))
        𝑢pre𝑥↦post𝑥 = ↓closed-lemma 𝑥 sub
                      (shrinklam sub⊆𝑓′ lam𝑢𝑥↦𝑔)
        𝑢x𝑥↦post = Appmap.↦-mono 𝑢 pre𝑥⊑x𝑥 𝑢pre𝑥↦post𝑥
        𝑢x𝑥↦y = Appmap.↦-↓closed 𝑢 y⊑post' 𝑢x𝑥↦post

β-lemma₂' : ∀ 𝑥 x′ y′ →
            [ 𝑢 ] ⟪ x′ , 𝑥 ⟫ ↦ ⟪ y′ ⟫ →
            ∀ x y → < x , y >ₛ ∈ₛ (< x′ , y′ >ₛ ∷ ∅) →
            [ 𝑢 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
β-lemma₂' _ _ _ 𝑢x′𝑥↦y′ _ _ here = 𝑢x′𝑥↦y′

β-lemma₂ : ∀ 𝑥 𝑦 →
           [ 𝑢 ∘ ⟨ idMap (nToCtx n) , 𝑡 ⟩ ] 𝑥 ↦ 𝑦 →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ 𝑦
β-lemma₂ _ ⟪ ⊥ᵤ , ⟪⟫ ⟫ _ = ap↦-intro₁
β-lemma₂ {n = n} {𝑢 = 𝑢} 𝑥 ⟪ λᵤ 𝑓 , ⟪⟫ ⟫
  (∘↦-intro _ ⟪ x , 𝑥′ ⟫ _
  (⟨⟩↦-intro _ _ (id↦-intro _ _ 𝑥′⊑𝑥) 𝑡𝑥↦x) 𝑢x𝑥′↦y)
  = ap↦-intro₂ x y (< x , y >ₛ ∷ ∅) lam𝑥↦xy 𝑡𝑥↦x
    (NbhSys.⊑-refl UniType)
  where y = λᵤ 𝑓
        x𝑥′⊑x𝑥 = ⊑ᵥ-cons (nToCtx (suc n)) ⟪ x , 𝑥′ ⟫
                 ⟪ x , 𝑥 ⟫ (NbhSys.⊑-refl UniType) 𝑥′⊑𝑥
        𝑢x𝑥↦y = Appmap.↦-mono 𝑢 x𝑥′⊑x𝑥 𝑢x𝑥′↦y
        lam𝑥↦xy = lam↦-intro₂ 𝑥 (< x , y >ₛ ∷ ∅)
                  (β-lemma₂' {𝑢 = 𝑢} 𝑥 x y 𝑢x𝑥↦y)

β-equal : ap (lam 𝑢) 𝑡 ≈ (𝑢 ∘ ⟨ idMap (nToCtx m) , 𝑡 ⟩)
β-equal = ≈-intro (≼-intro β-lemma₁) (≼-intro β-lemma₂)
