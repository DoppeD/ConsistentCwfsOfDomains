{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.ap.AxiomProofs
  {Γ : Ctx n}
  {𝐴 𝐵 : Ty}
  (𝑡 : tAppmap Γ [ ArrNbhSys 𝐴 𝐵 ])
  (𝑢 : tAppmap Γ [ 𝐴 ])
  where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵

ap↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 →
           [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑧 → [ 𝑡 , 𝑢 ] 𝑦 ap↦ 𝑧
ap↦-mono _ (ap↦-intro₁ p) = ap↦-intro₁ p
ap↦-mono {𝑥} {𝑦} 𝑥⊑𝑦 (ap↦-intro₂ x y 𝑓 _ _ 𝑡𝑥↦𝑓 𝑢𝑥↦x xy⊑𝑓)
  = ap↦-intro₂ x y 𝑓 _ _ 𝑡𝑦↦𝑓 𝑢𝑦↦x xy⊑𝑓
  where 𝑡𝑦↦𝑓 = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦𝑓
        𝑢𝑦↦x = Appmap.↦-mono 𝑢 𝑥⊑𝑦 𝑢𝑥↦x
ap↦-bottom : ∀ {𝑥} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ ⟪ NbhSys.⊥ 𝐵 , ⟪⟫ ⟫
ap↦-bottom = ap↦-intro₁ (NbhSys.⊑-refl 𝐵)

ap↦-↓closed' : ∀ {𝑓 x y y′} → ∀ conxy con𝑓 → [ 𝐵 ] y′ ⊑ y →
               [ ArrNbhSys 𝐴 𝐵 ] 𝐹 (< x , y > ∷ ∅)  conxy ⊑ 𝐹 𝑓 con𝑓 →
               ∀ x″ y″ → < x″ , y″ > ∈ (< x , y′ > ∷ ∅) →
               ⊑ₑ-proof 𝑓 con𝑓 x″ y″
ap↦-↓closed' {x = x} {y} {y′} conxy con𝑓 y′⊑y (⊑ₑ-intro₂ _ _ _ _ p) _ _ here
  = record { sub = sub
           ; y⊑post = NbhSys.⊑-trans 𝐵 y′⊑y y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  where paxy = p x y here
        sub = ⊑ₑ-proof.sub paxy
        pre⊑x = ⊑ₑ-proof.pre⊑x paxy
        y⊑post = ⊑ₑ-proof.y⊑post paxy
        sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 paxy

ap↦-↓closed : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ [ 𝐵 ] 𝑦 𝑧 →
              [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑧 → [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑦
ap↦-↓closed {𝑦 = ⟪ y , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ ⟪ y′ , ⟪⟫ ⟫ y⊑y′ ⊑ᵥ-nil) (ap↦-intro₁ y′⊑⊥)
  = ap↦-intro₁ (NbhSys.⊑-trans 𝐵 y⊑y′ y′⊑⊥)
ap↦-↓closed {𝑦 = ⟪ y , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ ⟪ y′ , ⟪⟫ ⟫ y⊑y′ ⊑ᵥ-nil)
  (ap↦-intro₂ x′ y′ 𝑓 _ _ 𝑡𝑥↦𝑓 𝑢𝑥↦x′ x′y′⊑𝑓′)
  = ap↦-intro₂ x′ y 𝑓 _ _ 𝑡𝑥↦𝑓 𝑢𝑥↦x′ x′y⊑𝑓
  where x′y⊑𝑓' = ap↦-↓closed' _ _ y⊑y′ x′y′⊑𝑓′
        x′y⊑𝑓 = ⊑ₑ-intro₂ (< x′ , y > ∷ ∅) 𝑓 singletonIsCon _ x′y⊑𝑓'
{-
ap↦-↑directed''' : ∀ {x y z 𝑔} → ∀ con𝑦𝑧 →
                   [ ArrNbhSys 𝐴 𝐵 ] 𝐹 (< x , y > ∷ ∅) ⊑ 𝐹 𝑔 →
                   [ 𝐵 ] z ⊑ NbhSys.⊥ 𝐵 → ∀ x′ y′ →
                   < x′ , y′ > ∈ (< x , [ 𝐵 ] y ⊔ z [ con𝑦𝑧 ] > ∷ ∅) →
                   ⊑ₑ-proof 𝑔 x′ y′
ap↦-↑directed''' {x = x} {y} (⊑ₑ-intro₂ _ _ p) _ _ _ here
  with (p x y here)
ap↦-↑directed''' (⊑ₑ-intro₂ _ _ p) z⊑⊥ x _ here
  | record { sub = sub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = record { sub = sub
           ; y⊑post = NbhSys.⊑-⊔ 𝐵 y⊑post
                      (NbhSys.⊑-trans 𝐵 z⊑⊥ (NbhSys.⊑-⊥ 𝐵))
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
           -}
{-
ap↦-↑directed'' : ∀ x y z 𝑔 →
                  [ ArrNbhSys 𝐴 𝐵 ] 𝐹 (< x , z > ∷ ∅) ⊑ 𝐹 𝑔 →
                  [ 𝐵 ] y ⊑ NbhSys.⊥ 𝐵 → ∀ x′ y′ →
                  < x′ , y′ > ∈ (< x , [ 𝐵 ] y ⊔ z > ∷ ∅) →
                  ⊑ₑ-proof 𝑔 x′ y′
ap↦-↑directed'' x _ z _ (⊑ₑ-intro₂ _ _ p) _ _ _ here
  with (p x z here)
ap↦-↑directed'' x y z _ _ y⊑⊥ _ _ here
  | record { sub = sub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = record { sub = sub
           ; y⊑post = NbhSys.⊑-⊔ 𝐵 (NbhSys.⊑-trans 𝐵 y⊑⊥
                      (NbhSys.⊑-⊥ 𝐵)) y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }

ap↦-↑directed' : {𝑓 𝑓′ : NbhFinFun 𝐴 𝐵} → ∀ {x x′ y y′} →
                 𝐹 (< x , y > ∷ ∅) ⊑ₑ 𝐹 𝑓 →
                 𝐹 (< x′ , y′ > ∷ ∅) ⊑ₑ 𝐹 𝑓′ → ∀ x″ y″ →
                 < x″ , y″ > ∈ (< [ 𝐴 ] x ⊔ x′ , [ 𝐵 ] y ⊔ y′ > ∷ ∅) →
                 ⊑ₑ-proof (𝑓 ∪ 𝑓′) x″ y″
ap↦-↑directed' {x = x} {x′} {y} {y′} (⊑ₑ-intro₂ _ _ p₁)
  (⊑ₑ-intro₂ _ _ p₂) x″ y″ here
  = record { sub = p₁sub ∪ p₂sub
           ; y⊑post = NbhSys.⊑-trans 𝐵
                      (⊑-⊔-lemma₃ 𝐵 p₁y⊑post p₂y⊑post)
                      (postLemma₁ p₁sub p₂sub)
           ; pre⊑x = NbhSys.⊑-trans 𝐴
                     (preLemma₁ p₁sub p₂sub)
                     (⊑-⊔-lemma₃ 𝐴 p₁pre⊑x p₂pre⊑x)
           ; sub⊆𝑓 = ∪-lemma₅ p₁sub⊆𝑓 p₂sub⊆𝑓
           }
  where p₁xyh = p₁ x y here
        p₂x′y′h = p₂ x′ y′ here
        p₁sub = ⊑ₑ-proof.sub p₁xyh
        p₂sub = ⊑ₑ-proof.sub p₂x′y′h
        p₁y⊑post = ⊑ₑ-proof.y⊑post p₁xyh
        p₂y⊑post = ⊑ₑ-proof.y⊑post p₂x′y′h
        p₁pre⊑x = ⊑ₑ-proof.pre⊑x p₁xyh
        p₂pre⊑x = ⊑ₑ-proof.pre⊑x p₂x′y′h
        p₁sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 p₁xyh
        p₂sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 p₂x′y′h

ap↦-↑directed : ∀ {𝑥 𝑦 𝑧} →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑦 → [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑧 →
                [ 𝑡 , 𝑢 ] 𝑥 ap↦ (𝑦 ⊔ᵥ 𝑧)
ap↦-↑directed (ap↦-intro₁ p₁) (ap↦-intro₁ p₂)
  = ap↦-intro₁ (NbhSys.⊑-⊔ 𝐵 p₁ p₂)
ap↦-↑directed {𝑦 = ⟪ y , ⟪⟫ ⟫} {⟪ z , ⟪⟫ ⟫} (ap↦-intro₁ p)
  (ap↦-intro₂ x′ _ 𝑔′ 𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′z⊑𝑔′)
  = ap↦-intro₂ x′ ([ 𝐵 ] y ⊔ z) 𝑔′ 𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′y⊔z⊑𝑔′
  where x′y⊔z⊑𝑔′ = ⊑ₑ-intro₂ (< x′ , [ 𝐵 ] y ⊔ z > ∷ ∅) 𝑔′
                   (ap↦-↑directed'' x′ y z 𝑔′ x′z⊑𝑔′ p)
ap↦-↑directed {𝑦 = ⟪ y , ⟪⟫ ⟫} {⟪ z , ⟪⟫ ⟫}
  (ap↦-intro₂ x _ 𝑔 𝑡𝑥↦𝑔 𝑢𝑥↦x xy⊑𝑔) (ap↦-intro₁ p)
  = ap↦-intro₂ x ([ 𝐵 ] y ⊔ z) 𝑔 𝑡𝑥↦𝑔 𝑢𝑥↦x xy⊔z⊑𝑔
    where xy⊔z⊑𝑔 = ⊑ₑ-intro₂ (< x , [ 𝐵 ] y ⊔ z > ∷ ∅) 𝑔
                   (ap↦-↑directed''' xy⊑𝑔 p)
ap↦-↑directed {𝑦 = ⟪ y , ⟪⟫ ⟫} {⟪ z , ⟪⟫ ⟫}
  (ap↦-intro₂ x _ 𝑔 𝑡𝑥↦𝑔 𝑢𝑥↦x xy⊑𝑔)
  (ap↦-intro₂ x′ _ 𝑔′ 𝑡𝑥↦𝑔′ 𝑢𝑥↦x′ x′z⊑𝑔′)
  = ap↦-intro₂ ([ 𝐴 ] x ⊔ x′) ([ 𝐵 ] y ⊔ z) (𝑔 ∪ 𝑔′)
    𝑡𝑥↦𝑔∪𝑔′ 𝑢𝑥↦x⊔x′ ⊔⊑∪
  where 𝑡𝑥↦𝑔∪𝑔′ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦𝑔 𝑡𝑥↦𝑔′
        𝑢𝑥↦x⊔x′ = Appmap.↦-↑directed 𝑢 𝑢𝑥↦x 𝑢𝑥↦x′
        ⊔⊑∪ = ⊑ₑ-intro₂ (< [ 𝐴 ] x ⊔ x′ , [ 𝐵 ] y ⊔ z > ∷ ∅)
              (𝑔 ∪ 𝑔′) (ap↦-↑directed' xy⊑𝑔 x′z⊑𝑔′)
-}

ap↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑦 →
          [ 𝑡 , 𝑢 ] 𝑥′ ap↦ 𝑦′ → ValCon _ 𝑥 𝑥′ →
          ValCon _ 𝑦 𝑦′
ap↦-con {𝑦′ = ⟪ y' , ⟪⟫ ⟫} (ap↦-intro₁ y⊑⊥) ap𝑥′↦𝑦′ _
  = NbhSys.Con-⊔ (ValNbhSys [ 𝐵 ]) 𝑦⊑𝑦′ 𝑦′⊑𝑦′
  where 𝑦′⊑𝑦′ = NbhSys.⊑-refl (ValNbhSys _)
        y⊑y′ = NbhSys.⊑-trans 𝐵 y⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        𝑦⊑𝑦′ = ⊑ᵥ-cons _ _ _ y⊑y′ ⊑ᵥ-nil
ap↦-con (ap↦-intro₂ _ _ _ _ _ _ _ _) (ap↦-intro₁ y′⊑⊥) _
  = NbhSys.Con-⊔ (ValNbhSys [ 𝐵 ]) 𝑦⊑𝑦 𝑦′⊑𝑦
  where 𝑦⊑𝑦 = NbhSys.⊑-refl (ValNbhSys _)
        y′⊑y = NbhSys.⊑-trans 𝐵 y′⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        𝑦′⊑𝑦 = ⊑ᵥ-cons _ _ _ y′⊑y ⊑ᵥ-nil
ap↦-con (ap↦-intro₂ x y 𝑓 con𝑓 conxy 𝑡𝑥↦𝑓 𝑢𝑥↦x xy⊑𝑓)
  (ap↦-intro₂ x′ y′ 𝑓′ con𝑓′ conx′y′ 𝑡𝑥′↦𝑓′ 𝑢𝑥′↦x′ x′y′⊑𝑓′)
  con𝑥𝑥′
  = {!!}
