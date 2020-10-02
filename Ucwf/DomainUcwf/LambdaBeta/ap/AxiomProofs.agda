{-# OPTIONS --safe --sized-types #-}

open import Ucwf.DomainUcwf.Appmap.Definition
open import Base.Variables

module Ucwf.DomainUcwf.LambdaBeta.ap.AxiomProofs
  {𝑡 𝑢 : uAppmap n 1} where

open import NbhSys.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.ap.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.DomainUcwf.UniType.PrePost
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.Transitivity
open import Ucwf.DomainUcwf.UniType.SizedFinFun

private
  UT : NbhSys
  UT = UniType

ap↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ (nToCtx n) 𝑥 𝑦 →
           [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑧 → [ 𝑡 , 𝑢 ] 𝑦 ap↦ 𝑧
ap↦-mono _ ap↦-intro₁ = ap↦-intro₁
ap↦-mono 𝑥⊑𝑦 (ap↦-intro₂ 𝑡𝑥↦𝑓 𝑢𝑥↦x xy⊑𝑓)
  = ap↦-intro₂ 𝑡𝑦↦𝑓 𝑢𝑦↦x xy⊑𝑓
  where 𝑡𝑦↦𝑓 = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦𝑓
        𝑢𝑦↦x = Appmap.↦-mono 𝑢 𝑥⊑𝑦 𝑢𝑥↦x

ap↦-bottom : ∀ {𝑥} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ ⟪ ⊥ᵤ ⟫
ap↦-bottom = ap↦-intro₁

ap↦-↓closed' : ∀ {𝑓′ x y 𝑓} →
               [ UT ] (λᵤ 𝑓) ⊑ y →
               [ UT ] λᵤ ((x , y) ∷ ∅) ⊑ λᵤ 𝑓′ →
               ∀ x′ y′ →
               (x′ , y′) ∈ₛ ((x , λᵤ 𝑓) ∷ ∅) →
               ⊑ᵤ-proof 𝑓′ x′ y′
ap↦-↓closed' {x = x} {y} 𝑓⊑y (⊑ᵤ-intro₂ _ _ p) _ _ here
  = record { sub = sub
           ; y⊑ᵤpost = NbhSys.⊑-trans UT 𝑓⊑y y⊑post
           ; pre⊑ᵤx = pre⊑x
           ; sub⊆𝑓′ = sub⊆𝑓
           }
  where paxy = p x y here
        sub = ⊑ᵤ-proof.sub paxy
        pre⊑x = ⊑ᵤ-proof.pre⊑ᵤx paxy
        y⊑post = ⊑ᵤ-proof.y⊑ᵤpost paxy
        sub⊆𝑓 = ⊑ᵤ-proof.sub⊆𝑓′ paxy

ap↦-↓closed : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ (nToCtx 1) 𝑦 𝑧 →
              [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑧 → [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑦
ap↦-↓closed {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} _ _ = ap↦-intro₁
ap↦-↓closed {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫} (⊑ᵥ-cons _ 𝑓⊑y ⊑ᵥ-nil)
  (ap↦-intro₂ {x = x′} {𝑓 = 𝑓′} 𝑡𝑥↦𝑓′ 𝑢𝑥↦x′ x′y′⊑𝑓′)
  = ap↦-intro₂ 𝑡𝑥↦𝑓′ 𝑢𝑥↦x′ x′𝑓⊑𝑓′
  where x′𝑓⊑𝑓′' = ap↦-↓closed' 𝑓⊑y x′y′⊑𝑓′
        x′𝑓⊑𝑓′ = ⊑ᵤ-intro₂ ((x′ , λᵤ 𝑓) ∷ ∅) 𝑓′ x′𝑓⊑𝑓′'

ap↦-↑directed' : ∀ {𝑓 𝑓′ x x′ y y′} →
                 λᵤ ((x , y) ∷ ∅) ⊑ᵤ (λᵤ 𝑓) →
                 λᵤ ((x′ , y′) ∷ ∅) ⊑ᵤ (λᵤ 𝑓′) → ∀ x″ y″ →
                 (x″ , y″) ∈ₛ
                 (((x ⊔ᵤ x′ [ con-all ]) , (y ⊔ᵤ y′ [ con-all ])) ∷ ∅) →
                 ⊑ᵤ-proof (𝑓 ∪ₛ 𝑓′) x″ y″
ap↦-↑directed' {x = x} {x′} {y} {y′} (⊑ᵤ-intro₂ _ _ p₁)
  (⊑ᵤ-intro₂ _ _ p₂) x″ y″ here
  = record { sub = p₁sub ∪ₛ p₂sub
           ; y⊑ᵤpost = Ω-post {𝑓 = p₁sub} p₁y⊑post p₂y⊑post
           ; pre⊑ᵤx = Ω-pre {𝑓 = p₁sub} p₁pre⊑x p₂pre⊑x
           ; sub⊆𝑓′ = ∪ₛ-lemma₅ p₁sub⊆𝑓 p₂sub⊆𝑓
           }
  where p₁xyh    = p₁ x y here
        p₂x′y′h  = p₂ x′ y′ here
        p₁sub    = ⊑ᵤ-proof.sub p₁xyh
        p₂sub    = ⊑ᵤ-proof.sub p₂x′y′h
        p₁y⊑post = ⊑ᵤ-proof.y⊑ᵤpost p₁xyh
        p₂y⊑post = ⊑ᵤ-proof.y⊑ᵤpost p₂x′y′h
        p₁pre⊑x = ⊑ᵤ-proof.pre⊑ᵤx p₁xyh
        p₂pre⊑x = ⊑ᵤ-proof.pre⊑ᵤx p₂x′y′h
        p₁sub⊆𝑓 = ⊑ᵤ-proof.sub⊆𝑓′ p₁xyh
        p₂sub⊆𝑓 = ⊑ᵤ-proof.sub⊆𝑓′ p₂x′y′h

ap↦-↑directed : ∀ {𝑥 𝑦 𝑧} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑦 →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑧 → (con𝑦𝑧 : ValCon _ 𝑦 𝑧) →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ (𝑦 ⊔ᵥ 𝑧 [ con𝑦𝑧 ])
ap↦-↑directed {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} {⟪ ⊥ᵤ ,, ⟪⟫ ⟫}
  𝑥↦𝑦 _ (con-tup _ _) = 𝑥↦𝑦
ap↦-↑directed {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} {⟪ λᵤ 𝑓′ ,, ⟪⟫ ⟫}
  _ 𝑥↦𝑧 (con-tup _ _) = 𝑥↦𝑧
ap↦-↑directed {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫} {⟪ ⊥ᵤ ,, ⟪⟫ ⟫}
  𝑥↦𝑦 _ (con-tup _ _) = 𝑥↦𝑦
ap↦-↑directed {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫} {⟪ λᵤ 𝑓′ ,, ⟪⟫ ⟫}
  (ap↦-intro₂ {x} {_} {𝑔} 𝑡𝑥↦𝑔 𝑢𝑥↦x x𝑓⊑𝑔)
  (ap↦-intro₂ {x′} {_} {𝑔′} 𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′𝑓′⊑𝑔′)
  (con-tup _ _)
  = ap↦-intro₂ 𝑡𝑥↦𝑔∪𝑔′ 𝑢𝑥↦x⊔x′ big⊑
    where 𝑡𝑥↦𝑔∪𝑔′ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦𝑔 𝑡𝑥↦𝑔′
                    (con-tup con-all con-nil)
          𝑢𝑥↦x⊔x′ = Appmap.↦-↑directed 𝑢 𝑢𝑥↦x 𝑢𝑥↦x′
                    (con-tup con-all con-nil)
          𝑓∪𝑓′ = λᵤ (𝑓 ∪ₛ 𝑓′)
          big⊑ = ⊑ᵤ-intro₂ (([ UT ] x ⊔ x′ [ con-all ] , 𝑓∪𝑓′) ∷ ∅)
                 (𝑔 ∪ₛ 𝑔′) (ap↦-↑directed' x𝑓⊑𝑔 x′𝑓′⊑𝑔′)
