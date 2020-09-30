{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.apSub (𝐴 𝐵 : Ty) where

open import Appmap.Equivalence
open import Base.FinFun
open import Base.Variables hiding (𝐴 ; 𝐵)
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Appmap.Identity.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation

private
  variable
    γ : tAppmap Δ Γ
    𝑡 : tAppmap Γ [ ArrNbhSys 𝐴 𝐵 ]
    𝑢 : tAppmap Γ [ 𝐴 ]

apSubLemma₁ : ∀ 𝑥 𝑦 → [ ap (𝑡 ∘ γ) (𝑢 ∘ γ) ] 𝑥 ↦ 𝑦 →
              [ ap 𝑡 𝑢 ∘ γ ] 𝑥 ↦ 𝑦
apSubLemma₁ {𝑡 = 𝑡} {γ = γ} {𝑢} 𝑥 ⟪ y , ⟪⟫ ⟫ (ap↦-intro₁ p)
  = Appmap.↦-↓closed (ap 𝑡 𝑢 ∘ γ) tupy⊑⊥ ap𝑡𝑢∘γ↦⊥
  where tupy⊑⊥ = ⊑ᵥ-cons [ 𝐵 ] p ⊑ᵥ-nil
        ap𝑡𝑢∘γ↦⊥ = Appmap.↦-bottom (ap 𝑡 𝑢 ∘ γ)
apSubLemma₁ {𝑡 = 𝑡} {γ = γ} {𝑢} 𝑥 _
  (ap↦-intro₂ _ _ (∘↦-intro _ 𝑦 _ γ𝑥↦𝑦 𝑡𝑦↦𝑓)
  (∘↦-intro _ 𝑧 _ γ𝑥↦𝑧 𝑢𝑧↦x) xy⊑𝑓)
  = ∘↦-intro 𝑥 _ _ γ𝑥↦𝑦⊔𝑧 ap𝑡𝑢𝑦𝑧↦y
  where con𝑦𝑧 = Appmap.↦-con γ γ𝑥↦𝑦 γ𝑥↦𝑧 valConRefl
        γ𝑥↦𝑦⊔𝑧 = Appmap.↦-↑directed γ γ𝑥↦𝑦 γ𝑥↦𝑧 con𝑦𝑧
        𝑡𝑦𝑧↦𝑓 = Appmap.↦-mono 𝑡 (NbhSys.⊑-⊔-fst (ValNbhSys _) _) 𝑡𝑦↦𝑓
        𝑢𝑦𝑧↦x = Appmap.↦-mono 𝑢 (NbhSys.⊑-⊔-snd (ValNbhSys _) _) 𝑢𝑧↦x
        ap𝑡𝑢𝑦𝑧↦y = ap↦-intro₂ _ _ 𝑡𝑦𝑧↦𝑓 𝑢𝑦𝑧↦x xy⊑𝑓

apSubLemma₂ : ∀ 𝑥 𝑦 → [ ap 𝑡 𝑢 ∘ γ ] 𝑥 ↦ 𝑦 →
              [ ap (𝑡 ∘ γ) (𝑢 ∘ γ) ] 𝑥 ↦ 𝑦
apSubLemma₂ {𝑡 = 𝑡} {𝑢} {γ = γ} 𝑥 ⟪ y , ⟪⟫ ⟫
  (∘↦-intro _ 𝑧 _ γ𝑥↦𝑧 (ap↦-intro₁ p))
  = Appmap.↦-↓closed (ap (𝑡 ∘ γ) (𝑢 ∘ γ)) tupy⊑⊥ ap𝑡∘γ𝑢∘γ↦⊥
  where tupy⊑⊥ = ⊑ᵥ-cons [ 𝐵 ] p ⊑ᵥ-nil
        ap𝑡∘γ𝑢∘γ↦⊥ = Appmap.↦-bottom (ap (𝑡 ∘ γ) (𝑢 ∘ γ))
apSubLemma₂ 𝑥 _ (∘↦-intro _ 𝑧 _ γ𝑥↦𝑧
  (ap↦-intro₂ _ _ 𝑡𝑧↦𝑓 𝑢𝑧↦x xy⊑𝑓))
  = ap↦-intro₂ _ _ 𝑡∘γ𝑥↦𝑓 𝑢∘γ𝑥↦x xy⊑𝑓
  where 𝑡∘γ𝑥↦𝑓 = ∘↦-intro _ _ _ γ𝑥↦𝑧 𝑡𝑧↦𝑓
        𝑢∘γ𝑥↦x = ∘↦-intro _ _ _ γ𝑥↦𝑧 𝑢𝑧↦x

apSub : {Γ : Ctx n} → (γ : tAppmap Δ Γ) → ∀ 𝑡 𝑢 →
        (ap (𝑡 ∘ γ) (𝑢 ∘ γ)) ≈ ((ap 𝑡 𝑢) ∘ γ)
apSub γ 𝑡 𝑢 = ≈-intro (≼-intro apSubLemma₁)
              (≼-intro apSubLemma₂)
