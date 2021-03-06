{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.ap.AxiomProofs
  {Γ : Ctx n}
  {𝐴 𝐵 : Ty}
  (𝑡 : Term Γ (𝐴 ⇒ 𝐵))
  (𝑢 : Term Γ 𝐴)
  where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵

ap↦-mono : ∀ {𝑥 𝑦 z} → ⊑ᵥ Γ 𝑥 𝑦 →
           [ 𝑡 , 𝑢 ] 𝑥 ap↦ z → [ 𝑡 , 𝑢 ] 𝑦 ap↦ z
ap↦-mono _ (ap↦-intro₁ p) = ap↦-intro₁ p
ap↦-mono {𝑥} {𝑦} 𝑥⊑𝑦 (ap↦-intro₂ _ _ 𝑡𝑥↦𝑓 𝑢𝑥↦x xy⊑𝑓)
  = ap↦-intro₂ _ _ 𝑡𝑦↦𝑓 𝑢𝑦↦x xy⊑𝑓
  where 𝑡𝑦↦𝑓 = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦𝑓
        𝑢𝑦↦x = Appmap.↦-mono 𝑢 𝑥⊑𝑦 𝑢𝑥↦x

ap↦-bottom : ∀ {𝑥} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ (NbhSys.⊥ 𝐵)
ap↦-bottom = ap↦-intro₁ (NbhSys.⊑-refl 𝐵)

ap↦-↓closed' : ∀ {𝑓 x y y′} → ∀ conxy con𝑓 → [ 𝐵 ] y′ ⊑ y →
               [ 𝐴 ⇒ 𝐵 ] 𝐹 ((x , y) ∷ ∅)  conxy ⊑ 𝐹 𝑓 con𝑓 →
               ∀ {x″ y″} → (x″ , y″) ∈ ((x , y′) ∷ ∅) →
               ⊑ₑ-proof 𝑓 con𝑓 x″ y″
ap↦-↓closed' conxy con𝑓 y′⊑y (⊑ₑ-intro₂ _ _ p) here
  = record { sub = sub
           ; y⊑post = NbhSys.⊑-trans 𝐵 y′⊑y y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  where paxy = p here
        sub = ⊑ₑ-proof.sub paxy
        pre⊑x = ⊑ₑ-proof.pre⊑x paxy
        y⊑post = ⊑ₑ-proof.y⊑post paxy
        sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 paxy

ap↦-↓closed : ∀ {𝑥 y z} → [ 𝐵 ] y ⊑ z →
              [ 𝑡 , 𝑢 ] 𝑥 ap↦ z → [ 𝑡 , 𝑢 ] 𝑥 ap↦ y
ap↦-↓closed y⊑y′ (ap↦-intro₁ y′⊑⊥)
  = ap↦-intro₁ (NbhSys.⊑-trans 𝐵 y⊑y′ y′⊑⊥)
ap↦-↓closed y⊑y′ (ap↦-intro₂ _ _ 𝑡𝑥↦𝑓 𝑢𝑥↦x′ x′y′⊑𝑓′)
  = ap↦-intro₂ _ _ 𝑡𝑥↦𝑓 𝑢𝑥↦x′ x′y⊑𝑓
  where x′y⊑𝑓' = ap↦-↓closed' _ _ y⊑y′ x′y′⊑𝑓′
        x′y⊑𝑓 = ⊑ₑ-intro₂ singletonIsCon _ x′y⊑𝑓'

ap↦-↑directed''' : ∀ {x y z 𝑔 con𝑔 conxy} → ∀ conyz →
                   [ 𝐴 ⇒ 𝐵 ] (𝐹 ((x , y) ∷ ∅) conxy) ⊑ (𝐹 𝑔 con𝑔) →
                   [ 𝐵 ] z ⊑ NbhSys.⊥ 𝐵 → ∀ {x′ y′} →
                   (x′ , y′) ∈ ((x , [ 𝐵 ] y ⊔ z [ conyz ]) ∷ ∅) →
                   ⊑ₑ-proof 𝑔 con𝑔 x′ y′
ap↦-↑directed''' {x = x} {y} _ (⊑ₑ-intro₂ _ _ p) _ here
  with (p here)
ap↦-↑directed''' conyz (⊑ₑ-intro₂ _ _ p) z⊑⊥ here
  | record { sub = sub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = record { sub = sub
           ; y⊑post = NbhSys.⊑-⊔ 𝐵 y⊑post
                      (NbhSys.⊑-trans 𝐵 z⊑⊥ (NbhSys.⊑-⊥ 𝐵))
                      conyz
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }

ap↦-↑directed'' : ∀ x y z 𝑔 → ∀ {con𝑔 conxz} → ∀ conyz →
                  [ 𝐴 ⇒ 𝐵 ] (𝐹 ((x , z) ∷ ∅) conxz) ⊑ (𝐹 𝑔 con𝑔) →
                  [ 𝐵 ] y ⊑ NbhSys.⊥ 𝐵 → ∀ {x′ y′} →
                  (x′ , y′) ∈ ((x , [ 𝐵 ] y ⊔ z [ conyz ]) ∷ ∅) →
                  ⊑ₑ-proof 𝑔 con𝑔 x′ y′
ap↦-↑directed'' x _ z _ _ (⊑ₑ-intro₂ _ _ p) _ here
  with (p here)
ap↦-↑directed'' x y z _ conyz _ y⊑⊥ here
  | record { sub = sub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = record { sub = sub
           ; y⊑post = NbhSys.⊑-⊔ 𝐵 (NbhSys.⊑-trans 𝐵 y⊑⊥
                      (NbhSys.⊑-⊥ 𝐵)) y⊑post
                      conyz
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }

ap↦-↑directed' : {𝑓 𝑓′ : NbhFinFun 𝐴 𝐵} → ∀ {x x′ y y′ con𝑓 con𝑓′ con∪} →
                 ∀ conxx′ conyy′ conxy conx′y′ →
                 (𝐹 ((x , y) ∷ ∅) conxy) ⊑ₑ (𝐹 𝑓 con𝑓) →
                 (𝐹 ((x′ , y′) ∷ ∅) conx′y′) ⊑ₑ (𝐹 𝑓′ con𝑓′) →
                 ∀ {x″ y″} →
                 (x″ , y″) ∈ (([ 𝐴 ] x ⊔ x′ [ conxx′ ] ,
                   [ 𝐵 ] y ⊔ y′ [ conyy′ ]) ∷ ∅) →
                 ⊑ₑ-proof (𝑓 ∪ 𝑓′) con∪ x″ y″
ap↦-↑directed' {con∪ = cff con∪} conxx′ conyy′ _ _
  (⊑ₑ-intro₂ _ _ p₁) (⊑ₑ-intro₂ _ _ p₂) here
  = record { sub = p₁sub ∪ p₂sub
           ; y⊑post = NbhSys.⊑-trans 𝐵
                      (⊑-⊔-lemma₃ 𝐵 conyy′ conposts p₁y⊑post p₂y⊑post)
                      (postLemma₃ p₁postable p₂postable postable∪ conposts)
           ; pre⊑x = NbhSys.⊑-trans 𝐴
                     (preLemma₃ p₁preable p₂preable preable∪ conpres)
                     (⊑-⊔-lemma₃ 𝐴 conpres conxx′ p₁pre⊑x p₂pre⊑x)
           ; sub⊆𝑓 = ∪-lemma₅ p₁sub⊆𝑓 p₂sub⊆𝑓
           }
  where p₁xyh = p₁ here
        p₂x′y′h = p₂ here
        p₁sub = ⊑ₑ-proof.sub p₁xyh
        p₂sub = ⊑ₑ-proof.sub p₂x′y′h
        p₁y⊑post = ⊑ₑ-proof.y⊑post p₁xyh
        p₂y⊑post = ⊑ₑ-proof.y⊑post p₂x′y′h
        p₁pre⊑x = ⊑ₑ-proof.pre⊑x p₁xyh
        p₂pre⊑x = ⊑ₑ-proof.pre⊑x p₂x′y′h
        p₁sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 p₁xyh
        p₂sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 p₂x′y′h
        p₁postable = ⊑ₑ-proof.postablesub p₁xyh
        p₂postable = ⊑ₑ-proof.postablesub p₂x′y′h
        p₁preable = ⊑ₑ-proof.preablesub p₁xyh
        p₂preable = ⊑ₑ-proof.preablesub p₂x′y′h
        p₁pre⊑x⊔x′ = ⊑-⊔-lemma₄ 𝐴 p₁pre⊑x conxx′
        p₂pre⊑x⊔x′ = ⊑-⊔-lemma₅ 𝐴 p₂pre⊑x conxx′
        conpres = NbhSys.Con-⊔ 𝐴 p₁pre⊑x⊔x′ p₂pre⊑x⊔x′
        preable∪ = preUnionLemma p₁preable p₂preable
                   p₁pre⊑x⊔x′ p₂pre⊑x⊔x′
        postable∪ = con∪ (∪-lemma₅ p₁sub⊆𝑓 p₂sub⊆𝑓) preable∪
        conposts = NbhSys.Con-⊔ 𝐵 {z = post (p₁sub ∪ p₂sub) postable∪}
                   (postLemma₁ {postable𝑓 = p₁postable} {postable∪})
                   (postLemma₂ {postable𝑓′ = p₂postable} {postable∪})

ap↦-↑directed : ∀ {𝑥 y z} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ y →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ z → ∀ conyz →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ ([ 𝐵 ] y ⊔ z [ conyz ])
ap↦-↑directed (ap↦-intro₁ p₁) (ap↦-intro₁ p₂) _
  = ap↦-intro₁ (NbhSys.⊑-⊔ 𝐵 p₁ p₂ _)
ap↦-↑directed (ap↦-intro₁ p)
  (ap↦-intro₂ con𝑔′ conxz  𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′z⊑𝑔′) _
  = ap↦-intro₂ con𝑔′ singletonIsCon 𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′y⊔z⊑𝑔′
  where x′y⊔z⊑𝑔′ = ⊑ₑ-intro₂ _ _
                   (ap↦-↑directed'' _ _ _ _ _ x′z⊑𝑔′ p)
ap↦-↑directed (ap↦-intro₂ _ _ 𝑡𝑥↦𝑔 𝑢𝑥↦x xy⊑𝑔) (ap↦-intro₁ p) _
  = ap↦-intro₂ _ singletonIsCon 𝑡𝑥↦𝑔 𝑢𝑥↦x xy⊔z⊑𝑔
  where xy⊔z⊑𝑔 = ⊑ₑ-intro₂ _ _ (ap↦-↑directed''' _ xy⊑𝑔 p)
ap↦-↑directed (ap↦-intro₂ _ _ 𝑡𝑥↦𝑔 𝑢𝑥↦x xy⊑𝑔)
  (ap↦-intro₂ _ _ 𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′z⊑𝑔′) _
  with (Appmap.↦-con 𝑡 𝑡𝑥↦𝑔 𝑡𝑥↦𝑔′ valConRefl)
... | con-∪ _ _ con𝑔∪𝑔′ =
  ap↦-intro₂ con𝑔∪𝑔′ singletonIsCon 𝑡𝑥↦𝑔∪𝑔′ 𝑢𝑥↦x⊔x′ ⊔⊑∪
  where conxx′ = Appmap.↦-con 𝑢 𝑢𝑥↦x 𝑢𝑥↦x′ valConRefl
        𝑡𝑥↦𝑔∪𝑔′ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦𝑔 𝑡𝑥↦𝑔′
                  (con-∪ _ _ con𝑔∪𝑔′)
        𝑢𝑥↦x⊔x′ = Appmap.↦-↑directed 𝑢 𝑢𝑥↦x 𝑢𝑥↦x′
                  conxx′
        ⊔⊑∪ = ⊑ₑ-intro₂ _ con𝑔∪𝑔′
              (ap↦-↑directed' conxx′ _ _ _ xy⊑𝑔 x′z⊑𝑔′)
