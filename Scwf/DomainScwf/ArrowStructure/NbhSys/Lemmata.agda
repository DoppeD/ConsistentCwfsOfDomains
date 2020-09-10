{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Lemmata
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.PrePost 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

open import Agda.Builtin.Equality

⊥⊥=∅₁ : [ ArrNbhSys 𝐴 𝐵 ]
        (𝐹 ∅) ⊑ (𝐹 (< NbhSys.⊥ 𝐴 , NbhSys.⊥ 𝐵 > ∷ ∅))
⊥⊥=∅₁ = ⊑ₑ-intro₂ ∅ (< NbhSys.⊥ 𝐴 , NbhSys.⊥ 𝐵 > ∷ ∅)
        λ x y → xy∈∅-abs

⊥⊥=∅₂' : ∀ x y →
         < x , y > ∈ (< NbhSys.⊥ 𝐴 , NbhSys.⊥ 𝐵 > ∷ ∅) →
         ⊑ₑ-proof ∅ x y
⊥⊥=∅₂' _ _ here
  = record { sub = ∅
           ; y⊑post = NbhSys.⊑-⊥ 𝐵
           ; pre⊑x = NbhSys.⊑-⊥ 𝐴
           ; sub⊆𝑓 = ⊆-refl
           }

⊥⊥=∅₂ : [ ArrNbhSys 𝐴 𝐵 ]
        (𝐹 (< NbhSys.⊥ 𝐴 , NbhSys.⊥ 𝐵 > ∷ ∅)) ⊑ (𝐹 ∅)
⊥⊥=∅₂ = ⊑ₑ-intro₂ ⊥⊥ ∅ ⊥⊥=∅₂'
  where ⊥⊥ = < NbhSys.⊥ 𝐴 , NbhSys.⊥ 𝐵 > ∷ ∅

-- The first component of any pair in a FinFun 𝑓 is smaller than pre 𝑓.
preBiggest : (𝑓 : NbhFinFun 𝐴 𝐵) → ∀ x y → < x , y > ∈ 𝑓 →
             [ 𝐴 ] x ⊑ pre 𝑓
preBiggest (< x , y > ∷ 𝑓′) x y here = NbhSys.⊑-⊔-fst 𝐴
preBiggest (< x′ , y′ > ∷ 𝑓′) x y (there xy∈𝑓′)
  = ⊑-⊔-lemma₅ 𝐴 (preBiggest 𝑓′ x y xy∈𝑓′)

⊥⊔x≡x : ∀ x → ⊥ₑ ⊔ₑ x ≡ x
⊥⊔x≡x ⊥ₑ = refl
⊥⊔x≡x (𝐹 𝑓) = refl

x⊔⊥≡x : ∀ x → x ⊔ₑ ⊥ₑ ≡ x
x⊔⊥≡x ⊥ₑ = refl
x⊔⊥≡x (𝐹 𝑓) = refl
