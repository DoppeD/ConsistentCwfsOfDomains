{-# OPTIONS --safe --sized-types #-}

open import Base.Variables
open import Ucwf.DomainUcwf.Appmap.Definition

open import Agda.Builtin.Nat

module Ucwf.DomainUcwf.LambdaBeta.lam.AxiomProofs
  {𝑡 : uAppmap (suc n) 1} where

open import Base.Core
open import NbhSys.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.lam.Lemmata
open import Ucwf.DomainUcwf.LambdaBeta.lam.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.DomainUcwf.UniType.PrePost
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.SizedFinFun

lam↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ (nToCtx n) 𝑥 𝑦 →
            [ 𝑡 ] 𝑥 lam↦ 𝑧 → [ 𝑡 ] 𝑦 lam↦ 𝑧
lam↦-mono {𝑦 = 𝑦} 𝑥⊑𝑦 lam↦-intro₁ = lam↦-intro₁
lam↦-mono {𝑥 = 𝑥} {𝑦 = 𝑦} 𝑥⊑𝑦 (lam↦-intro₂ _ 𝑓 p)
  = lam↦-intro₂ 𝑦 𝑓 λ x y xy∈𝑓 → Appmap.↦-mono 𝑡
    (⊑ᵥ-cons (nToCtx (suc n)) ⟪ x , 𝑥 ⟫ ⟪ x , 𝑦 ⟫
    (NbhSys.⊑-refl UniType) 𝑥⊑𝑦) (p x y xy∈𝑓)

lam↦-bottom : ∀ {𝑥} → [ 𝑡 ] 𝑥 lam↦ ⟪ ⊥ᵤ ⟫
lam↦-bottom = lam↦-intro₁

lam↦-↓closed' : ∀ {𝑥 𝑓 𝑓′} → [ UniType ] λᵤ 𝑓 ⊑ λᵤ 𝑓′ →
                [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓′ ⟫ →
                ∀ x y → < x , y >ₛ ∈ₛ 𝑓 →
                [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
lam↦-↓closed' (⊑ᵤ-intro₂ _ _ p) _ x y xy∈𝑓 with (p x y xy∈𝑓)
lam↦-↓closed' {𝑥 = 𝑥} _ 𝑡𝑥↦𝑓′ x y xy∈𝑓
  | record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = sub⊆𝑓′
           }
  = Appmap.↦-↓closed 𝑡 y⊑post' 𝑡x𝑥↦post
  where y⊑post' = ⊑ᵥ-cons (nToCtx 1) ⟪ y ⟫ ⟪ post sub ⟫
                  y⊑ᵤpost ⊑ᵥ-nil
        pre⊑post = ⊑ᵥ-cons (nToCtx (suc n)) ⟪ pre sub , 𝑥 ⟫
                   ⟪ x , 𝑥 ⟫ pre⊑ᵤx
                   (NbhSys.⊑-refl (ValNbhSys _))
        𝑡pre𝑥↦post = ↓closed-lemma 𝑥 sub
                     (shrinklam sub⊆𝑓′ 𝑡𝑥↦𝑓′)
        𝑡x𝑥↦post = Appmap.↦-mono 𝑡 pre⊑post 𝑡pre𝑥↦post

lam↦-↓closed : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ (nToCtx 1) 𝑦 𝑧 →
               [ 𝑡 ] 𝑥 lam↦ 𝑧 → [ 𝑡 ] 𝑥 lam↦ 𝑦
lam↦-↓closed {𝑦 = ⟪ ⊥ᵤ , _ ⟫} {⟪ 𝑧 , _ ⟫}
  (⊑ᵥ-cons _ _ _ 𝑦⊑𝑧 ⊑ᵥ-nil) 𝑡𝑥↦𝑧 = lam↦-intro₁
lam↦-↓closed {𝑥 = 𝑥} {⟪ λᵤ 𝑓 , _ ⟫} {⟪ λᵤ 𝑓′ , _ ⟫}
  (⊑ᵥ-cons _ _ _ 𝑓⊑𝑓′ ⊑ᵥ-nil) 𝑡𝑥↦𝑓′
  = lam↦-intro₂ 𝑥 𝑓 (lam↦-↓closed' 𝑓⊑𝑓′ 𝑡𝑥↦𝑓′)

lam↦-↑directed' : ∀ {𝑥 𝑓 𝑓′} → [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓 ⟫ →
                  [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓′ ⟫ → ∀ x y →
                  < x , y >ₛ ∈ₛ (𝑓 ∪ₛ 𝑓′) →
                  [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
lam↦-↑directed' {𝑓 = 𝑓} _ _ x y xy∈𝑓∪𝑓′
  with (∪ₛ-lemma₂ {𝑓 = 𝑓} < x , y >ₛ xy∈𝑓∪𝑓′)
lam↦-↑directed' (lam↦-intro₂ _ _ p) _ x y _
  | inl xy∈𝑓 = p x y xy∈𝑓
lam↦-↑directed' _ (lam↦-intro₂ _ _ p) x y _
  | inr xy∈𝑓′ = p x y xy∈𝑓′

lam↦-↑directed : ∀ {𝑥 𝑦 𝑧} → [ 𝑡 ] 𝑥 lam↦ 𝑦 →
                 [ 𝑡 ] 𝑥 lam↦ 𝑧 →
                 [ 𝑡 ] 𝑥 lam↦ (𝑦 ⊔ᵥ 𝑧)
lam↦-↑directed {𝑦 = ⟪ ⊥ᵤ , ⟪⟫ ⟫} {⟪ ⊥ᵤ , ⟪⟫ ⟫} _ 𝑡𝑥lam↦𝑧
  = 𝑡𝑥lam↦𝑧
lam↦-↑directed {𝑦 = ⟪ λᵤ 𝑓 , ⟪⟫ ⟫} {⟪ ⊥ᵤ , ⟪⟫ ⟫} 𝑡𝑥lam↦𝑦 _
  = 𝑡𝑥lam↦𝑦
lam↦-↑directed {𝑦 = ⟪ ⊥ᵤ , ⟪⟫ ⟫} {⟪ λᵤ 𝑓′ , ⟪⟫ ⟫} _ 𝑡𝑥lam↦𝑧
  = 𝑡𝑥lam↦𝑧
lam↦-↑directed {𝑥 = 𝑥} {⟪ λᵤ 𝑓 , ⟪⟫ ⟫} {⟪ λᵤ 𝑓′ , ⟪⟫ ⟫}
  𝑡𝑥lam↦𝑓 𝑡𝑥lam↦𝑓′
  = lam↦-intro₂ 𝑥 (𝑓 ∪ₛ 𝑓′) 𝑡x𝑥↦y
  where 𝑡x𝑥↦y = lam↦-↑directed' 𝑡𝑥lam↦𝑓 𝑡𝑥lam↦𝑓′
