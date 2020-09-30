{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.apSub where

open import Appmap.Equivalence
open import NbhSys.Definition
open import Base.Variables
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.ap.Instance
open import Ucwf.DomainUcwf.LambdaBeta.ap.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance

private
  variable
    γ : uAppmap n m
    𝑡 𝑢 : uAppmap m 1

apSubLemma₁ : ∀ {𝑥 𝑦} → [ ap (𝑡 ∘ γ) (𝑢 ∘ γ) ] 𝑥 ↦ 𝑦 →
              [ ap 𝑡 𝑢 ∘ γ ] 𝑥 ↦ 𝑦
apSubLemma₁ {γ = γ} {𝑦 = ⟪ ⊥ᵤ ,, _ ⟫} ap↦-intro₁ =
  ∘↦-intro (Appmap.↦-bottom γ) ap↦-intro₁
apSubLemma₁ {γ = γ} {𝑦 = ⟪ ⊥ᵤ ,, _ ⟫} (ap↦-intro₂ x y 𝑓
  (∘↦-intro γ𝑥↦𝑦 𝑡𝑦↦𝑓) (∘↦-intro γ𝑥↦𝑧 𝑢𝑧↦x) xy⊑𝑓)
  = ∘↦-intro (Appmap.↦-bottom γ) ap↦-intro₁
apSubLemma₁ {𝑡 = 𝑡} {γ = γ} {𝑢 = 𝑢} {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫}
  (ap↦-intro₂ x y 𝑔 (∘↦-intro γ𝑥↦𝑦 𝑡𝑦↦𝑔)
  (∘↦-intro γ𝑥↦𝑧 𝑢𝑧↦x) xy⊑𝑔)
  = ∘↦-intro γ𝑥↦𝑦⊔𝑧 ap𝑡𝑢𝑦𝑧↦y
  where 𝑦⊑𝑦⊔𝑧 = NbhSys.⊑-⊔-fst (ValNbhSys _) valConAll
        𝑡𝑦𝑧↦𝑔 = Appmap.↦-mono 𝑡 𝑦⊑𝑦⊔𝑧 𝑡𝑦↦𝑔
        𝑧⊑𝑦⊔𝑧 = NbhSys.⊑-⊔-snd (ValNbhSys _) valConAll
        𝑢𝑦𝑧↦x = Appmap.↦-mono 𝑢 𝑧⊑𝑦⊔𝑧 𝑢𝑧↦x
        ap𝑡𝑢𝑦𝑧↦y = ap↦-intro₂ x (λᵤ 𝑓) 𝑔 𝑡𝑦𝑧↦𝑔 𝑢𝑦𝑧↦x xy⊑𝑔
        γ𝑥↦𝑦⊔𝑧 = Appmap.↦-↑directed γ γ𝑥↦𝑦 γ𝑥↦𝑧 valConAll

apSubLemma₂ : ∀ {𝑥 𝑦} → [ ap 𝑡 𝑢 ∘ γ ] 𝑥 ↦ 𝑦 →
              [ ap (𝑡 ∘ γ) (𝑢 ∘ γ) ] 𝑥 ↦ 𝑦
apSubLemma₂ {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} _ = ap↦-intro₁
apSubLemma₂ {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫}
  (∘↦-intro γ𝑥↦𝑧 (ap↦-intro₂ x _ 𝑔 𝑡𝑧↦𝑔 𝑢𝑧↦x x𝑓⊑𝑔))
  = ap↦-intro₂ x (λᵤ 𝑓) 𝑔 𝑡∘γ𝑥↦𝑓 𝑢∘γ𝑥↦x x𝑓⊑𝑔
  where 𝑡∘γ𝑥↦𝑓 = ∘↦-intro γ𝑥↦𝑧 𝑡𝑧↦𝑔
        𝑢∘γ𝑥↦x = ∘↦-intro γ𝑥↦𝑧 𝑢𝑧↦x

apSub : (γ : uAppmap n m) → ∀ 𝑡 𝑢 →
        (ap (𝑡 ∘ γ) (𝑢 ∘ γ)) ≈ ((ap 𝑡 𝑢) ∘ γ)
apSub γ 𝑡 𝑢 = ≈-intro (≼-intro apSubLemma₁)
              (≼-intro (apSubLemma₂))
