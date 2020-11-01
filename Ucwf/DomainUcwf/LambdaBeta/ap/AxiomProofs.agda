{-# OPTIONS --safe --sized-types #-}

open import Ucwf.DomainUcwf.Appmap.Definition
open import Base.Variables

module Ucwf.DomainUcwf.LambdaBeta.ap.AxiomProofs
  {𝑡 𝑢 : uTerm n} where

open import Base.Core
open import Base.FinFun
open import NbhSys.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.ap.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.DomainUcwf.UniType.PrePost
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.Transitivity

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

ap↦-bottom : ∀ {𝑥} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ ⊥ᵤ
ap↦-bottom = ap↦-intro₁

ap↦-↓closed' : ∀ {𝑓′ x y 𝑓} →
               [ UT ] (λᵤ 𝑓) ⊑ y →
               [ UT ] λᵤ ((x , y) ∷ ∅) ⊑ λᵤ 𝑓′ →
               ∀ x′ y′ →
               (x′ , y′) ∈ ((x , λᵤ 𝑓) ∷ ∅) →
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

ap↦-↓closed : ∀ {𝑥 y z} → [ UniType ] y ⊑ z →
              [ 𝑡 , 𝑢 ] 𝑥 ap↦ z → [ 𝑡 , 𝑢 ] 𝑥 ap↦ y
ap↦-↓closed {y = ⊥ᵤ} _ _ = ap↦-intro₁
ap↦-↓closed {y = λᵤ 𝑓} 𝑓⊑y
  (ap↦-intro₂ {x = x′} {𝑓 = 𝑓′} 𝑡𝑥↦𝑓′ 𝑢𝑥↦x′ x′y′⊑𝑓′)
  = ap↦-intro₂ 𝑡𝑥↦𝑓′ 𝑢𝑥↦x′ x′𝑓⊑𝑓′
  where x′𝑓⊑𝑓′' = ap↦-↓closed' 𝑓⊑y x′y′⊑𝑓′
        x′𝑓⊑𝑓′ = ⊑ᵤ-intro₂ ((x′ , λᵤ 𝑓) ∷ ∅) 𝑓′ x′𝑓⊑𝑓′'

ap↦-↑directed' : ∀ {𝑓 𝑓′ x x′ y y′} →
                 λᵤ ((x , y) ∷ ∅) ⊑ᵤ (λᵤ 𝑓) →
                 λᵤ ((x′ , y′) ∷ ∅) ⊑ᵤ (λᵤ 𝑓′) → ∀ x″ y″ →
                 (x″ , y″) ∈
                 (((x ⊔ᵤ x′ [ con-all ]) , (y ⊔ᵤ y′ [ con-all ])) ∷ ∅) →
                 ⊑ᵤ-proof (𝑓 ∪ 𝑓′) x″ y″
ap↦-↑directed' {x = x} {x′} {y} {y′} (⊑ᵤ-intro₂ _ _ p₁)
  (⊑ᵤ-intro₂ _ _ p₂) x″ y″ here
  = record { sub = p₁sub ∪ p₂sub
           ; y⊑ᵤpost = Ω-post {𝑓 = p₁sub} p₁y⊑post p₂y⊑post
           ; pre⊑ᵤx = Ω-pre {𝑓 = p₁sub} p₁pre⊑x p₂pre⊑x
           ; sub⊆𝑓′ = ∪-lemma₅ p₁sub⊆𝑓 p₂sub⊆𝑓
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

ap↦-↑directed : ∀ {𝑥 y z} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ y →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ z → ∀ conyz →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ ([ UniType ] y ⊔ z [ conyz ])
ap↦-↑directed {y = ⊥ᵤ} {⊥ᵤ} 𝑥↦𝑦 _ _ = 𝑥↦𝑦
ap↦-↑directed {y = ⊥ᵤ} {λᵤ 𝑓′} _ 𝑥↦𝑧 _ = 𝑥↦𝑧
ap↦-↑directed {y = λᵤ 𝑓} {⊥ᵤ} 𝑥↦𝑦 _ _ = 𝑥↦𝑦
ap↦-↑directed {y = λᵤ 𝑓} {λᵤ 𝑓′}
  (ap↦-intro₂ {x} {_} {𝑔} 𝑡𝑥↦𝑔 𝑢𝑥↦x x𝑓⊑𝑔)
  (ap↦-intro₂ {x′} {_} {𝑔′} 𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′𝑓′⊑𝑔′) _
  = ap↦-intro₂ 𝑡𝑥↦𝑔∪𝑔′ 𝑢𝑥↦x⊔x′ big⊑
    where 𝑡𝑥↦𝑔∪𝑔′ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦𝑔 𝑡𝑥↦𝑔′
                    con-all
          𝑢𝑥↦x⊔x′ = Appmap.↦-↑directed 𝑢 𝑢𝑥↦x 𝑢𝑥↦x′
                    con-all
          𝑓∪𝑓′ = λᵤ (𝑓 ∪ 𝑓′)
          big⊑ = ⊑ᵤ-intro₂ (([ UT ] x ⊔ x′ [ con-all ] , 𝑓∪𝑓′) ∷ ∅)
                 (𝑔 ∪ 𝑔′) (ap↦-↑directed' x𝑓⊑𝑔 x′𝑓′⊑𝑔′)
