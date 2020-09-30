{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.lam.AxiomProofs
  {𝐴 𝐵 : Ty}
  {Γ : Ctx n}
  (𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ]) where

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

lam↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 →
            [ 𝑡 ] 𝑥 lam↦ 𝑧 → [ 𝑡 ] 𝑦 lam↦ 𝑧
lam↦-mono _ lam↦-intro₁ = lam↦-intro₁
lam↦-mono {𝑥 = 𝑥} {𝑦} 𝑥⊑𝑦 (lam↦-intro₂ _ 𝑓 _ p)
  = lam↦-intro₂ _ _ _ λ x y xy∈𝑓 → Appmap.↦-mono 𝑡
    (⊑ᵥ-cons (𝐴 :: Γ) ⟪ x , 𝑥 ⟫ ⟪ x , 𝑦 ⟫
    (NbhSys.⊑-refl 𝐴) 𝑥⊑𝑦) (p x y xy∈𝑓)

lam↦-bottom : ∀ {𝑥} → [ 𝑡 ] 𝑥 lam↦ ⟪ ⊥ₑ ⟫
lam↦-bottom = lam↦-intro₁

lam↦-↓closed' : ∀ {𝑥 𝑓 𝑓′ con𝑓 con𝑓′} →
                [ ArrNbhSys 𝐴 𝐵 ] 𝐹 𝑓 con𝑓 ⊑ 𝐹 𝑓′ con𝑓′ →
                [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓′ con𝑓′ ⟫ → ∀ x y →
                < x , y > ∈ 𝑓 →
                [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
lam↦-↓closed' (⊑ₑ-intro₂ _ _ _ _ p) _ x y xy∈𝑓
  with (p x y xy∈𝑓)
lam↦-↓closed' {𝑥 = 𝑥} {con𝑓′ = con𝑓′} _ 𝑡𝑥↦𝑓′ x y xy∈𝑓
  | record { sub = sub
           ; preablesub = preablesub
           ; postablesub = postablesub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = Appmap.↦-↓closed 𝑡 y⊑post' 𝑡x𝑥↦post
  where y⊑post' = ⊑ᵥ-cons [ 𝐵 ] ⟪ y ⟫ ⟪ post sub _ ⟫
                  y⊑post ⊑ᵥ-nil
        pre⊑post = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ pre sub _ , 𝑥 ⟫
                   ⟪ x , 𝑥 ⟫ pre⊑x
                   (NbhSys.⊑-refl (ValNbhSys _))
        𝑡pre𝑥↦post = ↓closedLemma (subsetIsCon con𝑓′ sub⊆𝑓)
                     preablesub postablesub
                     (shrinkLam sub⊆𝑓 𝑡𝑥↦𝑓′)
        𝑡x𝑥↦post = Appmap.↦-mono 𝑡 pre⊑post 𝑡pre𝑥↦post

lam↦-↓closed : ∀ {𝑥 𝑦 𝑧} →
               ⊑ᵥ [ ArrNbhSys 𝐴 𝐵 ] 𝑦 𝑧 →
               [ 𝑡 ] 𝑥 lam↦ 𝑧 → [ 𝑡 ] 𝑥 lam↦ 𝑦
lam↦-↓closed {𝑦 = ⟪ _ , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ ⊑ₑ-intro₁ ⊑ᵥ-nil) lam↦-intro₁
  = lam↦-intro₁
lam↦-↓closed {𝑦 = ⟪ ⊥ₑ , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ y⊑𝑓′ ⊑ᵥ-nil) (lam↦-intro₂ _ 𝑓′ _ p)
  = lam↦-intro₁
lam↦-↓closed {𝑥 = 𝑥} {⟪ 𝐹 𝑓 _ , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ 𝑓⊑𝑓′ ⊑ᵥ-nil) (lam↦-intro₂ _ 𝑓′ _ p)
  = lam↦-intro₂ 𝑥 𝑓 _
    (lam↦-↓closed' 𝑓⊑𝑓′ (lam↦-intro₂ 𝑥 𝑓′ _ p))

lam↦-↑directed' : ∀ {𝑓 𝑓′ 𝑥 con𝑓 con𝑓′} →
                  [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 con𝑓 ⟫ →
                  [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓′ con𝑓′ ⟫ → ∀ x y →
                  < x , y > ∈ (𝑓 ∪ 𝑓′) →
                  [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
lam↦-↑directed' {𝑓 = 𝑓} _ _ x y xy∈𝑓⊔𝑓′
  with (∪-lemma₂ {𝑓 = 𝑓} xy∈𝑓⊔𝑓′)
lam↦-↑directed' (lam↦-intro₂ _ _ _ p) _ x y _ | inl xy∈𝑓
  = p x y xy∈𝑓
lam↦-↑directed' _ (lam↦-intro₂ _ _ _ p) x y _ | inr xy∈𝑓′
  = p x y xy∈𝑓′

lam↦-↑directed : ∀ {𝑥 𝑦 𝑧} →
                 [ 𝑡 ] 𝑥 lam↦ 𝑦 → [ 𝑡 ] 𝑥 lam↦ 𝑧 →
                 (con𝑦𝑧 : ValCon _ 𝑦 𝑧) →
                 [ 𝑡 ] 𝑥 lam↦ (𝑦 ⊔ᵥ 𝑧 [ con𝑦𝑧 ])
lam↦-↑directed {𝑥 = 𝑥} {𝑧 = ⟪ z , ⟪⟫ ⟫} lam↦-intro₁ 𝑡𝑥↦z
 (con-tup _ _ con⊥z _ _ _)
 rewrite (⊥⊔x≡x z {con⊥z}) = 𝑡𝑥↦z
lam↦-↑directed {𝑥 = 𝑥} (lam↦-intro₂ _ 𝑓 con𝑓 p) lam↦-intro₁
 (con-tup _ _ con𝑓z _ _ _)
  rewrite (x⊔⊥≡x (𝐹 𝑓 con𝑓) {con𝑓z}) = lam↦-intro₂ 𝑥 𝑓 _ p
lam↦-↑directed {𝑥 = 𝑥} (lam↦-intro₂ _ 𝑓 _ p₁)
  (lam↦-intro₂ _ 𝑓′ _ p₂)
 (con-tup _ _ (con-∪ con𝑓 con𝑓′ _) _ _ _)
  = lam↦-intro₂ 𝑥 (𝑓 ∪ 𝑓′) _ 𝑡x𝑥↦y
  where 𝑡x𝑥↦y = lam↦-↑directed'
                (lam↦-intro₂ _ _ con𝑓 p₁)
                (lam↦-intro₂ _ _ con𝑓′ p₂)
