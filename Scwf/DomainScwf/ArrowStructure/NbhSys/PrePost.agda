{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.PrePost
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata

pre : NbhFinFun 𝐴 𝐵 → NbhSys.Nbh 𝐴
pre ∅ = NbhSys.⊥ 𝐴
pre (< x , y > ∷ 𝑓) = [ 𝐴 ] x ⊔ (pre 𝑓)

post : NbhFinFun 𝐴 𝐵 → NbhSys.Nbh 𝐵
post ∅ = NbhSys.⊥ 𝐵
post (< x , y > ∷ 𝑓) = [ 𝐵 ] y ⊔ (post 𝑓)

preLemma₁ : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
            [ 𝐴 ] pre (𝑓 ∪ 𝑓′) ⊑ ([ 𝐴 ] pre 𝑓 ⊔ pre 𝑓′)
preLemma₁ ∅ 𝑓′
  = ⊑-⊔-lemma₅ 𝐴 (NbhSys.⊑-refl 𝐴)
preLemma₁ (< x , y > ∷ 𝑓″) 𝑓′
  = NbhSys.⊑-trans 𝐴 (⊑-⊔-lemma₃ 𝐴 (NbhSys.⊑-refl 𝐴)
    (preLemma₁ 𝑓″ 𝑓′)) (⊔-ass₂ 𝐴  (NbhSys.⊑-refl 𝐴))

postLemma₁ : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
             [ 𝐵 ] ([ 𝐵 ] post 𝑓 ⊔ post 𝑓′) ⊑ post (𝑓 ∪ 𝑓′)
postLemma₁ ∅ 𝑓′
  = NbhSys.⊑-⊔ 𝐵 (NbhSys.⊑-⊥ 𝐵) (NbhSys.⊑-refl 𝐵)
postLemma₁ (< x , y > ∷ 𝑓″) 𝑓′
  = ⊔-ass₁ 𝐵 (⊑-⊔-lemma₃ 𝐵 (NbhSys.⊑-refl 𝐵)
    (postLemma₁ 𝑓″ 𝑓′))
