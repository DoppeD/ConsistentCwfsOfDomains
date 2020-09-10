{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Transitivity
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.AxiomProofs 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.PrePost 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

-- This can be derived from 𝐹 𝑓 ⊑ₑ 𝐹 𝑓′, and makes proving
-- transitivity very simple.
record ⊑ₑ-proof₂ (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) : Set where
  field
    sub : NbhFinFun 𝐴 𝐵
    p𝑓⊑post : [ 𝐵 ] (post 𝑓) ⊑ (post sub)
    pre⊑p𝑓 : [ 𝐴 ] (pre sub) ⊑ (pre 𝑓)
    sub⊆𝑓′ : sub ⊆ 𝑓′

shrinkExp' : 𝑓 ⊆ 𝑓′ → (𝐹 𝑓′) ⊑ₑ (𝐹 𝑓″) →
             ∀ x y → < x , y > ∈ 𝑓 →
             ⊑ₑ-proof 𝑓″ x y
shrinkExp' 𝑓⊆𝑓′ (⊑ₑ-intro₂ 𝑓 𝑓′ p) x y xy∈𝑓
  = record { sub = ⊑ₑ-proof.sub shrinkIt
           ; y⊑post = ⊑ₑ-proof.y⊑post shrinkIt
           ; pre⊑x = ⊑ₑ-proof.pre⊑x shrinkIt
           ; sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 shrinkIt
           }
  where shrinkIt = p x y (𝑓⊆𝑓′ < x , y > xy∈𝑓)

-- If 𝑓 ⊆ 𝑓′ and 𝑓′ ⊑ₑ 𝑓″, then we can adapt the ⊑ₑ-proof
-- of 𝑓′ and 𝑓″ to one for 𝑓 and 𝑓″.
shrinkExp : 𝑓 ⊆ 𝑓′ → (𝐹 𝑓′) ⊑ₑ (𝐹 𝑓″) → (𝐹 𝑓) ⊑ₑ (𝐹 𝑓″)
shrinkExp {𝑓 = 𝑓} {𝑓″ = 𝑓″} 𝑓⊆𝑓′ 𝑓′⊑𝑓″
   = ⊑ₑ-intro₂ 𝑓 𝑓″ (shrinkExp' 𝑓⊆𝑓′ 𝑓′⊑𝑓″)

Ω : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) → (𝐹 𝑓) ⊑ₑ (𝐹 𝑓′) →
    ⊑ₑ-proof₂ 𝑓 𝑓′
Ω ∅ 𝑓′ 𝑓⊑𝑓′
  = record { sub = ∅
           ; p𝑓⊑post = NbhSys.⊑-refl 𝐵
           ; pre⊑p𝑓 = NbhSys.⊑-refl 𝐴
           ; sub⊆𝑓′ = ∅-isSubset
           }
Ω (< x , y > ∷ 𝑓″) 𝑓′ (⊑ₑ-intro₂ _ _ p) with (p x y here)
Ω (< x , y > ∷ 𝑓″) 𝑓′ (⊑ₑ-intro₂ _ _ p)
  | record { sub = sub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = record { sub = sub ∪ sub′
           ; p𝑓⊑post = NbhSys.⊑-trans 𝐵 (⊑-⊔-lemma₃ 𝐵 y⊑post
                       (⊑ₑ-proof₂.p𝑓⊑post recur))
                       (postLemma₁ sub sub′)
           ; pre⊑p𝑓 = NbhSys.⊑-trans 𝐴 (preLemma₁ sub sub′)
                      (⊑-⊔-lemma₃ 𝐴 pre⊑x
                      (⊑ₑ-proof₂.pre⊑p𝑓 recur))
           ; sub⊆𝑓′ = ∪-lemma₁ sub⊆𝑓 (⊑ₑ-proof₂.sub⊆𝑓′ recur)
           }
  where recur = Ω 𝑓″ 𝑓′ (shrinkExp (⊆-lemma₃ < x , y >)
                (⊑ₑ-intro₂ (< x , y > ∷ 𝑓″) 𝑓′ p))
        sub′ = ⊑ₑ-proof₂.sub recur

⊑ₑ-trans' : (𝐹 𝑓) ⊑ₑ (𝐹 𝑓′) → (𝐹 𝑓′) ⊑ₑ (𝐹 𝑓″) →
            ∀ x y → < x , y > ∈ 𝑓 →
            ⊑ₑ-proof 𝑓″ x y
⊑ₑ-trans' {𝑓} {𝑓′} {𝑓″} (⊑ₑ-intro₂ _ _ p₁)
  (⊑ₑ-intro₂ _ _ p₂) x y xy∈𝑓
  = record { sub = 𝑓″sub
           ; y⊑post = NbhSys.⊑-trans 𝐵
                      (⊑ₑ-proof.y⊑post 𝑓′proof)
                      (⊑ₑ-proof₂.p𝑓⊑post 𝑓″proof₂)
           ; pre⊑x = NbhSys.⊑-trans 𝐴 
                     (⊑ₑ-proof₂.pre⊑p𝑓 𝑓″proof₂)
                     (⊑ₑ-proof.pre⊑x 𝑓′proof)
           ; sub⊆𝑓 = ⊑ₑ-proof₂.sub⊆𝑓′ 𝑓″proof₂
           }
  where 𝑓′proof = p₁ x y xy∈𝑓
        𝑓′sub = ⊑ₑ-proof.sub 𝑓′proof
        𝑓″proof₂ = Ω 𝑓′sub 𝑓″ (shrinkExp
                   (⊑ₑ-proof.sub⊆𝑓 𝑓′proof)
                   (⊑ₑ-intro₂ 𝑓′ 𝑓″ p₂))
        𝑓″sub = ⊑ₑ-proof₂.sub 𝑓″proof₂

⊑ₑ-trans : ∀ {x y z} → x ⊑ₑ y → y ⊑ₑ z → x ⊑ₑ z
⊑ₑ-trans {x = ⊥ₑ} _ _ = ⊑ₑ-intro₁
⊑ₑ-trans {x = 𝐹 𝑓} {⊥ₑ} {⊥ₑ} x⊑y ⊑ₑ-intro₁ = x⊑y
⊑ₑ-trans {x = 𝐹 𝑓} {𝐹 𝑓′} {𝐹 𝑓″} x⊑y y⊑z
  = ⊑ₑ-intro₂ 𝑓 𝑓″ (⊑ₑ-trans' x⊑y y⊑z)
