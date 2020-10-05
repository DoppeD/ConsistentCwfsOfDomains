{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.lam.AxiomProofs
  {𝐴 𝐵 : Ty}
  {Γ : Ctx n}
  (𝑡 : Term (𝐴 :: Γ) 𝐵) where

open import Appmap.Lemmata
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.lam.Lemmata 𝐴 𝐵 𝑡
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

lam↦-mono : ∀ {𝑥 𝑦 z} → ⊑ᵥ Γ 𝑥 𝑦 →
            [ 𝑡 ] 𝑥 lam↦ z → [ 𝑡 ] 𝑦 lam↦ z
lam↦-mono _ lam↦-intro₁ = lam↦-intro₁
lam↦-mono 𝑥⊑𝑦 (lam↦-intro₂ _ p)
  = lam↦-intro₂ _ λ xy∈𝑓 → Appmap.↦-mono 𝑡
    (⊑ᵥ-cons (𝐴 :: Γ) (NbhSys.⊑-refl 𝐴) 𝑥⊑𝑦) (p xy∈𝑓)

lam↦-bottom : ∀ {𝑥} → [ 𝑡 ] 𝑥 lam↦ ⊥ₑ
lam↦-bottom = lam↦-intro₁

lam↦-↓closed' : ∀ {𝑥 𝑓 𝑓′ con𝑓 con𝑓′} →
                [ 𝐴 ⇒ 𝐵 ] 𝐹 𝑓 con𝑓 ⊑ 𝐹 𝑓′ con𝑓′ →
                [ 𝑡 ] 𝑥 lam↦ (𝐹 𝑓′ con𝑓′) → ∀ {x y} →
                (x , y) ∈ 𝑓 →
                [ 𝑡 ] ⟪ x ,, 𝑥 ⟫ ↦ y
lam↦-↓closed' (⊑ₑ-intro₂ _ _ p) _ xy∈𝑓
  with (p xy∈𝑓)
lam↦-↓closed' {𝑥 = 𝑥} {con𝑓′ = con𝑓′} _ 𝑡𝑥↦𝑓′ xy∈𝑓
  | record { sub = sub
           ; preablesub = preablesub
           ; postablesub = postablesub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = Appmap.↦-↓closed 𝑡 y⊑post 𝑡x𝑥↦post
  where pre⊑post = ⊑ᵥ-cons (𝐴 :: Γ) pre⊑x
                   (NbhSys.⊑-refl (ValNbhSys _))
        𝑡pre𝑥↦post = ↓closedLemma (subsetIsCon con𝑓′ sub⊆𝑓)
                     preablesub postablesub
                     (shrinkLam sub⊆𝑓 𝑡𝑥↦𝑓′)
        𝑡x𝑥↦post = Appmap.↦-mono 𝑡 pre⊑post 𝑡pre𝑥↦post

lam↦-↓closed : ∀ {𝑥 y z} → [ 𝐴 ⇒ 𝐵 ] y ⊑ z →
               [ 𝑡 ] 𝑥 lam↦ z → [ 𝑡 ] 𝑥 lam↦ y
lam↦-↓closed ⊑ₑ-intro₁ lam↦-intro₁
  = lam↦-intro₁
lam↦-↓closed {y = ⊥ₑ} y⊑𝑓′ (lam↦-intro₂ _ p)
  = lam↦-intro₁
lam↦-↓closed {𝑥 = 𝑥} {𝐹 𝑓 _} 𝑓⊑𝑓′ (lam↦-intro₂ _ p)
  = lam↦-intro₂ _ (lam↦-↓closed' 𝑓⊑𝑓′ (lam↦-intro₂ _ p))

lam↦-↑directed' : ∀ {𝑓 𝑓′ 𝑥 con𝑓 con𝑓′} →
                  [ 𝑡 ] 𝑥 lam↦ (𝐹 𝑓 con𝑓) →
                  [ 𝑡 ] 𝑥 lam↦ (𝐹 𝑓′ con𝑓′) → ∀ {x y} →
                  (x , y) ∈ (𝑓 ∪ 𝑓′) →
                  [ 𝑡 ] ⟪ x ,, 𝑥 ⟫ ↦ y
lam↦-↑directed' {𝑓 = 𝑓} _ _ xy∈𝑓⊔𝑓′
  with (∪-lemma₂ {𝑓 = 𝑓} xy∈𝑓⊔𝑓′)
lam↦-↑directed' (lam↦-intro₂ _ p) _ _ | inl xy∈𝑓
  = p xy∈𝑓
lam↦-↑directed' _ (lam↦-intro₂ _ p) _ | inr xy∈𝑓′
  = p xy∈𝑓′

lam↦-↑directed : ∀ {𝑥 y z} →
                 [ 𝑡 ] 𝑥 lam↦ y → [ 𝑡 ] 𝑥 lam↦ z →
                 ∀ conyz → [ 𝑡 ] 𝑥 lam↦ ([ 𝐴 ⇒ 𝐵 ] y ⊔ z [ conyz ])
lam↦-↑directed {z = z} lam↦-intro₁ 𝑡𝑥↦z conyz
 rewrite (⊥⊔x≡x z {conyz}) = 𝑡𝑥↦z
lam↦-↑directed (lam↦-intro₂ con𝑓 p) lam↦-intro₁ conyz
  rewrite (x⊔⊥≡x (𝐹 _ con𝑓) {conyz}) = lam↦-intro₂ _ p
lam↦-↑directed (lam↦-intro₂ _ p₁) (lam↦-intro₂ _ p₂)
 (con-∪ con𝑓 con𝑓′ _)
  = lam↦-intro₂ _ 𝑡x𝑥↦y
  where 𝑡x𝑥↦y = lam↦-↑directed' (lam↦-intro₂ con𝑓 p₁)
                (lam↦-intro₂ con𝑓′ p₂)
