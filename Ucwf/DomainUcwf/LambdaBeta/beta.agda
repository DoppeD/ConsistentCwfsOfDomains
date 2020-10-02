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

β-lemma₁ : ∀ {𝑥 𝑦} →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ 𝑦 →
           [ 𝑢 ∘ ⟨ idMap (nToCtx m) , 𝑡 ⟩ ] 𝑥 ↦ 𝑦
β-lemma₁ {m = m} {𝑢 = 𝑢} {𝑡 = 𝑡} {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} _
  = ∘↦-intro ⟨⟩⊥↦⊥ 𝑢⊥↦⊥
  where id⊥↦⊥ = Appmap.↦-bottom (idMap (nToCtx m))
        𝑡𝑥↦⊥ = Appmap.↦-bottom 𝑡
        ⟨⟩⊥↦⊥ = ⟨⟩↦-intro {𝑦 = ⟪ _ ,, ⊥ᵥ ⟫} id⊥↦⊥ 𝑡𝑥↦⊥
        𝑢⊥↦⊥ = Appmap.↦-bottom 𝑢
β-lemma₁ {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫}
  (ap↦-intro₂ _ _ (⊑ᵤ-intro₂ _ _ p))
  with (p _ _ here)
β-lemma₁ {m = m} {𝑢 = 𝑢} {𝑡 = 𝑡} {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫}
  (ap↦-intro₂ {x} lam𝑢𝑥↦𝑔 𝑡𝑥↦x _)
  | record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = sub⊆𝑓′
           }
  = ∘↦-intro (⟨⟩↦-intro {𝑦 = ⟪ x ,, _ ⟫} id𝑥↦𝑥 𝑡𝑥↦x) 𝑢x𝑥↦y
  where id𝑥↦𝑥 = id↦-intro (NbhSys.⊑-refl (ValNbhSys _))
        y⊑post' = ⊑ᵥ-cons [ UniType ] y⊑ᵤpost ⊑ᵥ-nil
        pre𝑥⊑x𝑥 = ⊑ᵥ-cons (nToCtx (suc m)) pre⊑ᵤx
                  (NbhSys.⊑-refl (ValNbhSys _))
        𝑢pre𝑥↦post𝑥 = ↓closed-lemma _ sub
                      (shrinklam sub⊆𝑓′ lam𝑢𝑥↦𝑔)
        𝑢x𝑥↦post = Appmap.↦-mono 𝑢 pre𝑥⊑x𝑥 𝑢pre𝑥↦post𝑥
        𝑢x𝑥↦y = Appmap.↦-↓closed 𝑢 y⊑post' 𝑢x𝑥↦post

β-lemma₂' : ∀ 𝑥 x′ y′ →
            [ 𝑢 ] ⟪ x′ ,, 𝑥 ⟫ ↦ ⟪ y′ ⟫ →
            ∀ {x y} → (x , y) ∈ₛ ((x′ , y′) ∷ ∅) →
            [ 𝑢 ] ⟪ x ,, 𝑥 ⟫ ↦ ⟪ y ⟫
β-lemma₂' _ _ _ 𝑢x′𝑥↦y′ here = 𝑢x′𝑥↦y′

β-lemma₂ : ∀ {𝑥 𝑦} →
           [ 𝑢 ∘ ⟨ idMap (nToCtx n) , 𝑡 ⟩ ] 𝑥 ↦ 𝑦 →
           [ ap (lam 𝑢) 𝑡 ] 𝑥 ↦ 𝑦
β-lemma₂ {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} _ = ap↦-intro₁
β-lemma₂ {n = n} {𝑢 = 𝑢} {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫}
  (∘↦-intro (⟨⟩↦-intro (id↦-intro 𝑥′⊑𝑥) 𝑡𝑥↦x) 𝑢x𝑥′↦y)
  = ap↦-intro₂ lam𝑥↦xy 𝑡𝑥↦x (NbhSys.⊑-refl UniType)
  where y = λᵤ 𝑓
        x𝑥′⊑x𝑥 = ⊑ᵥ-cons (nToCtx (suc n))
                 (NbhSys.⊑-refl UniType) 𝑥′⊑𝑥
        𝑢x𝑥↦y = Appmap.↦-mono 𝑢 x𝑥′⊑x𝑥 𝑢x𝑥′↦y
        lam𝑥↦xy = lam↦-intro₂ (β-lemma₂' {𝑢 = 𝑢} _ _ _ 𝑢x𝑥↦y)

β-equal : ap (lam 𝑢) 𝑡 ≈ (𝑢 ∘ ⟨ idMap (nToCtx m) , 𝑡 ⟩)
β-equal = ≈-intro (≼-intro β-lemma₁) (≼-intro β-lemma₂)
