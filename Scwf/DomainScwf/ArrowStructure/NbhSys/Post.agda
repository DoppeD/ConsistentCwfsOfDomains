{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Post
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

data Postable : NbhFinFun 𝐴 𝐵 → Set
post : (𝑓 : NbhFinFun 𝐴 𝐵) → Postable 𝑓 → NbhSys.Nbh 𝐵

data Postable where
  post-nil : Postable ∅
  post-cons : ∀ {x y 𝑓} → (postable𝑓 : Postable 𝑓) →
              NbhSys.Con 𝐵 y (post 𝑓 postable𝑓) → Postable ((x , y) ∷ 𝑓)

post ∅ _ = NbhSys.⊥ 𝐵
post ((x , y) ∷ 𝑓) (post-cons postable𝑓 conxpost𝑓)
  = [ 𝐵 ] y ⊔ post 𝑓 postable𝑓 [ conxpost𝑓 ]

boundedPostable' : ∀ {𝑓 postable𝑓 max} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → [ 𝐵 ] y ⊑ max) →
                   [ 𝐵 ] post 𝑓 postable𝑓 ⊑ max
boundedPostable' {∅} _ = NbhSys.⊑-⊥ 𝐵
boundedPostable' {(x , y) ∷ 𝑓}
  {postable𝑓 = post-cons postable𝑓 conypost𝑓} bound
  = NbhSys.⊑-⊔ 𝐵 (bound here) rec conypost𝑓
  where rec = boundedPostable' {postable𝑓 = postable𝑓}
                λ x′y′∈𝑓 → bound (there x′y′∈𝑓)

boundedPostable : ∀ {𝑓 max} →
                  (∀ {x y} → (x , y) ∈ 𝑓 → [ 𝐵 ] y ⊑ max) →
                  Postable 𝑓
boundedPostable {∅} _ = post-nil
boundedPostable {(x , y) ∷ 𝑓} bound
  = post-cons (boundedPostable {𝑓} (λ xy∈𝑓 → bound (there xy∈𝑓)))
    (NbhSys.Con-⊔ 𝐵 (bound here)
    (boundedPostable' {𝑓} λ xy∈𝑓 → bound (there xy∈𝑓)))

postableProofIrr : (postable𝑓₁ postable𝑓₂ : Postable 𝑓) →
                   [ 𝐵 ] (post 𝑓 postable𝑓₁) ⊑ (post 𝑓 postable𝑓₂)
postableProofIrr {∅} post-nil post-nil = NbhSys.⊑-refl 𝐵
postableProofIrr {(x , y) ∷ 𝑓} (post-cons postable𝑓₁ conxpost𝑓₁)
  (post-cons postable𝑓₂ conxpost𝑓₂)
  = ⊑-⊔-lemma₃ 𝐵 _ _ (NbhSys.⊑-refl 𝐵)
    (postableProofIrr postable𝑓₁ postable𝑓₂)

postLemma₁ : ∀ {𝑓 𝑓′ postable𝑓 postable∪} →
            [ 𝐵 ] post 𝑓 postable𝑓 ⊑ post (𝑓 ∪ 𝑓′) postable∪
postLemma₁ {postable𝑓 = post-nil} = NbhSys.⊑-⊥ 𝐵
postLemma₁ {𝑓 = _ ∷ 𝑓} {postable𝑓 = post-cons postable𝑓 conxpost𝑓}
  {post-cons postable𝑓∪𝑓′ conxpost∪}
  = ⊑-⊔-lemma₃ 𝐵 _ _ (NbhSys.⊑-refl 𝐵) rec
  where rec = postLemma₁ {𝑓 = 𝑓} {postable𝑓 = postable𝑓}

postLemma₂ : ∀ {𝑓 𝑓′ postable𝑓′ postable∪} →
            [ 𝐵 ] post 𝑓′ postable𝑓′ ⊑ post (𝑓 ∪ 𝑓′) postable∪
postLemma₂ {𝑓 = _} {∅} = NbhSys.⊑-⊥ 𝐵
postLemma₂ {𝑓 = ∅} {_ ∷ _} {postable𝑓′}
  = NbhSys.⊑-trans 𝐵 (NbhSys.⊑-refl 𝐵)
    (postableProofIrr postable𝑓′ _)
postLemma₂ {𝑓 = (x , y) ∷ 𝑓} {(x′ , y′) ∷ 𝑓′}
  {post-cons postable𝑓′tail conxpost𝑓′tail}
  {post-cons postable∪tail x′con∪tail}
  = ⊑-⊔-lemma₅ 𝐵 rec x′con∪tail
  where postable𝑓′ = post-cons postable𝑓′tail conxpost𝑓′tail
        rec = postLemma₂ {𝑓 = 𝑓} {𝑓′ = (x′ , y′) ∷ 𝑓′}
              {postable𝑓′ = postable𝑓′}

postLemma₃ : (postable𝑓 : Postable 𝑓) → (postable𝑓′ : Postable 𝑓′) →
             (postable∪ : Postable (𝑓 ∪ 𝑓′)) →
             (conpost : NbhSys.Con 𝐵 (post 𝑓 postable𝑓) (post 𝑓′ postable𝑓′)) →
             [ 𝐵 ] ([ 𝐵 ] (post 𝑓 postable𝑓) ⊔
             (post 𝑓′ postable𝑓′) [ conpost ])
             ⊑ (post (𝑓 ∪ 𝑓′) postable∪)
postLemma₃ postable𝑓 postable𝑓′ postable∪ conpost
  = NbhSys.⊑-⊔ 𝐵 post𝑓⊑post∪ post𝑓′⊑post∪ conpost
  where post𝑓⊑post∪ = postLemma₁ {postable𝑓 = postable𝑓} {postable∪}
        post𝑓′⊑post∪ = postLemma₂ {postable𝑓′ = postable𝑓′} {postable∪}

singletonIsPostable : ∀ {x y} → Postable ((x , y) ∷ ∅)
singletonIsPostable = post-cons post-nil (con⊥₂ 𝐵)
