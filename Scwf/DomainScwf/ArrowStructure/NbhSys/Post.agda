{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Post (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

data Postable : NbhFinFun 𝐴 𝐵 → Set
post : (f : NbhFinFun 𝐴 𝐵) → Postable f → NbhSys.Nbh 𝐵

data Postable where
  post-nil : Postable ∅
  post-cons : ∀ {x y f} → (postablef : Postable f) →
              NbhSys.Con 𝐵 y (post f postablef) → Postable (< x , y > ∷ f)

post ∅ _ = NbhSys.⊥ 𝐵
post (< x , y > ∷ f) (post-cons postablef conxpostf)
  = [ 𝐵 ] y ⊔ post f postablef [ conxpostf ]

BoundedPost : NbhFinFun 𝐴 𝐵 → Set
BoundedPost 𝑓
  = Σ (NbhSys.Nbh 𝐵) λ max → ∀ {x y} → < x , y > ∈ 𝑓 → [ 𝐵 ] y ⊑ max

boundedPostLemma : 𝑓 ⊆ 𝑓′ → BoundedPost 𝑓′ → BoundedPost 𝑓
boundedPostLemma 𝑓⊆𝑓′ boundedPost𝑓′
  = (fst boundedPost𝑓′) , λ xy∈𝑓 → snd boundedPost𝑓′ (𝑓⊆𝑓′ _ xy∈𝑓)

boundedPostLemmaEq : (𝑓⊆𝑓″ : 𝑓 ⊆ 𝑓″) → (𝑓′⊆𝑓″ : 𝑓′ ⊆ 𝑓″) →
                     (bp𝑓″ : BoundedPost 𝑓″) →
                     (fst (boundedPostLemma 𝑓⊆𝑓″ bp𝑓″)) ≡
                     (fst (boundedPostLemma 𝑓′⊆𝑓″ bp𝑓″))
boundedPostLemmaEq _ _ _ = refl

postableBounded' : (postable𝑓 : Postable 𝑓) →
                   ∀ {x′ y′} → < x′ , y′ > ∈ 𝑓 →
                   [ 𝐵 ] y′ ⊑ (post 𝑓 postable𝑓)
postableBounded' {< x , y > ∷ 𝑓} (post-cons postablef conxpostf) here
  = NbhSys.⊑-⊔-fst 𝐵 conxpostf
postableBounded' {< x , y > ∷ 𝑓} (post-cons postablef conxpostf) (there x′y′∈f)
  = NbhSys.⊑-trans 𝐵 (postableBounded' postablef x′y′∈f) (NbhSys.⊑-⊔-snd 𝐵 conxpostf)

postableBounded : Postable 𝑓 → BoundedPost 𝑓
postableBounded post-nil = (NbhSys.⊥ 𝐵) , xy∈∅-abs
postableBounded {< x , y > ∷ 𝑓′} (post-cons postable𝑓′ conxpost𝑓′)
  = [ 𝐵 ] y ⊔ post 𝑓′ postable𝑓′ [ conxpost𝑓′ ] ,
    postableBounded' (post-cons postable𝑓′ conxpost𝑓′)
  where 𝑓′bound = postableBounded postable𝑓′

postableLemma : (postable𝑓 : Postable 𝑓) →
                (boundedPost𝑓 : BoundedPost 𝑓) →
                [ 𝐵 ] (post 𝑓 postable𝑓) ⊑ (fst boundedPost𝑓)
postableLemma {∅} _ _ = NbhSys.⊑-⊥ 𝐵
postableLemma {< x , y > ∷ 𝑓} (post-cons postable𝑓 conxpost𝑓) boundedPostxy𝑓
  = NbhSys.⊑-⊔ 𝐵 ((snd boundedPostxy𝑓) here)
    (postableLemma postable𝑓 (boundedPostLemma (⊆-lemma₃ < x , y >) boundedPostxy𝑓))
    conxpost𝑓

boundedPostable : BoundedPost 𝑓 → Postable 𝑓
boundedPostable {∅} _ = post-nil
boundedPostable {< x , y > ∷ 𝑓} (max , maxProof)
  = post-cons postable𝑓 (NbhSys.Con-⊔ 𝐵 (maxProof here)
    (postableLemma postable𝑓 boundedpost𝑓))
  where boundedpost𝑓
          = boundedPostLemma (λ xy xy∈𝑓 → there xy∈𝑓) (max , maxProof)
        postable𝑓 = boundedPostable boundedpost𝑓

postableProofIrr : (postable𝑓₁ postable𝑓₂ : Postable 𝑓) →
                   [ 𝐵 ] (post 𝑓 postable𝑓₁) ⊑ (post 𝑓 postable𝑓₂)
postableProofIrr {∅} post-nil post-nil = NbhSys.⊑-refl 𝐵
postableProofIrr {< x , y > ∷ 𝑓} (post-cons postable𝑓₁ conxpost𝑓₁)
  (post-cons postable𝑓₂ conxpost𝑓₂)
  = ⊑-⊔-lemma₃ 𝐵 _ _ (NbhSys.⊑-refl 𝐵) (postableProofIrr postable𝑓₁ postable𝑓₂)

postLemma''' : (bound𝑓 : BoundedPost 𝑓) → (bound𝑓′ : BoundedPost 𝑓′) →
               (postable𝑓 : Postable 𝑓) → (postable𝑓′ : Postable 𝑓′) →
               fst bound𝑓 ≡ fst bound𝑓′ →
               NbhSys.Con 𝐵 (post 𝑓 postable𝑓) (post 𝑓′ postable𝑓′)
postLemma''' {𝑓} {𝑓′} (_ , snd₁) bound𝑓′ postable𝑓 postable𝑓′ refl
  = NbhSys.Con-⊔ 𝐵 (postableLemma postable𝑓 (fst bound𝑓′ , snd₁))
    (postableLemma postable𝑓′ bound𝑓′)

postLemma₁'' : (postable𝑓 : Postable 𝑓) → (postable𝑓′ : Postable 𝑓′) →
               (postable∪ : Postable (𝑓 ∪ 𝑓′)) →
               NbhSys.Con 𝐵 (post 𝑓 postable𝑓) (post 𝑓′ postable𝑓′)
postLemma₁'' {𝑓} {𝑓′} postable𝑓 postable𝑓′ postable∪
  = postLemma''' boundedPost𝑓 boundedPost𝑓′ postable𝑓 postable𝑓′ sameBound
    where boundedPost𝑓 = boundedPostLemma ∪-lemma₃ (postableBounded postable∪)
          boundedPost𝑓′ = boundedPostLemma ∪-lemma₄ (postableBounded postable∪)
          boundedPost𝑓″ = postableBounded postable∪
          sameBound = boundedPostLemmaEq {𝑓 = 𝑓} {𝑓′ = 𝑓′} ∪-lemma₃ ∪-lemma₄ boundedPost𝑓″

postLemma₁' : ∀ y → (postable𝑓 : Postable 𝑓) → (postable𝑓′ : Postable 𝑓′) →
              (con₁ : NbhSys.Con 𝐵 y (post 𝑓 postable𝑓)) →
              (con₂ : NbhSys.Con 𝐵 (post 𝑓 postable𝑓) (post 𝑓′ postable𝑓′)) →
              NbhSys.Con 𝐵 ([ 𝐵 ] y ⊔ post 𝑓 postable𝑓 [ con₁ ]) (post 𝑓′ postable𝑓′) →
              NbhSys.Con 𝐵 y ([ 𝐵 ] (post 𝑓 postable𝑓) ⊔ (post 𝑓′ postable𝑓′) [ con₂ ])
postLemma₁' {𝑓} {𝑓′} y postable𝑓 postable𝑓′ con₁ con₂ con₃
  = NbhSys.Con-⊔ 𝐵 (NbhSys.⊑-trans 𝐵 (NbhSys.⊑-⊔-fst 𝐵 con₁) (NbhSys.⊑-⊔-fst 𝐵 con₃))
    (⊑-⊔-lemma₃ 𝐵 _ _ (NbhSys.⊑-⊔-snd 𝐵 _) (NbhSys.⊑-refl 𝐵))

postLemma₁ : (postable𝑓 : Postable 𝑓) → (postable𝑓′ : Postable 𝑓′) →
             (postable∪ : Postable (𝑓 ∪ 𝑓′)) →
             (conpost : NbhSys.Con 𝐵 (post 𝑓 postable𝑓) (post 𝑓′ postable𝑓′)) →
             [ 𝐵 ] ([ 𝐵 ] (post 𝑓 postable𝑓) ⊔ (post 𝑓′ postable𝑓′) [ conpost ])
             ⊑ (post (𝑓 ∪ 𝑓′) postable∪)
postLemma₁ {∅} {𝑓′} post-nil _ _ _
  = NbhSys.⊑-⊔ 𝐵 (NbhSys.⊑-⊥ 𝐵) (postableProofIrr {𝑓 = 𝑓′} _ _) _
postLemma₁ {< x , y > ∷ 𝑓} {𝑓′} (post-cons postable𝑓 conxpost𝑓) postable𝑓′
  (post-cons postable∪ conxpost∪) conpost₁
  = ⊔-ass₁ 𝐵 _ conpost₂ conypost⊔ conpost₁
    (⊑-⊔-lemma₃ 𝐵 _ _ (NbhSys.⊑-refl 𝐵)
    (postLemma₁ {𝑓 = 𝑓} {𝑓′ = 𝑓′} _ _ _ _))
  where conpost₂ = postLemma₁'' postable𝑓 postable𝑓′ postable∪
        conypost⊔ = postLemma₁' y postable𝑓 postable𝑓′ conxpost𝑓 conpost₂ conpost₁

postUnionLemma' : ∀ {max} → (postable𝑓 : Postable 𝑓) →
                  (postable𝑓′ : Postable 𝑓′) → (postable∪ : Postable (𝑓 ∪ 𝑓′)) →
                  [ 𝐵 ] (post 𝑓 postable𝑓) ⊑ max → [ 𝐵 ] (post 𝑓′ postable𝑓′) ⊑ max →
                  [ 𝐵 ] (post (𝑓 ∪ 𝑓′) postable∪) ⊑ max
postUnionLemma' {∅} {𝑓′} postable𝑓 postable𝑓′ postable∪ post𝑓⊑max post𝑓′⊑max
  = NbhSys.⊑-trans 𝐵 (postableProofIrr postable∪ postable𝑓′) post𝑓′⊑max
postUnionLemma' {< x , y > ∷ 𝑓} (post-cons postable𝑓 conxpost𝑓) postable𝑓′
  (post-cons postable∪ conxpost∪) postxy𝑓⊑max post𝑓′⊑max
  = NbhSys.⊑-⊔ 𝐵 x⊑max rec conxpost∪
  where post𝑓⊑max = NbhSys.⊑-trans 𝐵 (NbhSys.⊑-⊔-snd 𝐵 conxpost𝑓) postxy𝑓⊑max
        rec = postUnionLemma' postable𝑓 postable𝑓′ postable∪ post𝑓⊑max post𝑓′⊑max
        x⊑max = NbhSys.⊑-trans 𝐵 (NbhSys.⊑-⊔-fst 𝐵 conxpost𝑓) postxy𝑓⊑max

postUnionLemma : ∀ {max} → (postable𝑓 : Postable 𝑓) →
                 (postable𝑓′ : Postable 𝑓′) → [ 𝐵 ] (post 𝑓 postable𝑓) ⊑ max →
                 [ 𝐵 ] (post 𝑓′ postable𝑓′) ⊑ max → Postable (𝑓 ∪ 𝑓′)
postUnionLemma {∅} _ postable𝑓′ _ _ = postable𝑓′
postUnionLemma {< x , y > ∷ 𝑓} (post-cons postable𝑓 conxpost𝑓) postable𝑓′ post𝑓⊑x post𝑓′⊑x
  = post-cons rec (NbhSys.Con-⊔ 𝐵 x⊑max post∪⊑max)
  where post𝑓⊑max = NbhSys.⊑-trans 𝐵 (NbhSys.⊑-⊔-snd 𝐵 conxpost𝑓) post𝑓⊑x
        rec = postUnionLemma postable𝑓 postable𝑓′ post𝑓⊑max post𝑓′⊑x
        x⊑max = NbhSys.⊑-trans 𝐵 (NbhSys.⊑-⊔-fst 𝐵 conxpost𝑓) post𝑓⊑x
        post∪⊑max = postUnionLemma' postable𝑓 postable𝑓′ rec post𝑓⊑max post𝑓′⊑x

singletonIsPostable : ∀ {x y} → Postable (< x , y > ∷ ∅)
singletonIsPostable = post-cons post-nil (con⊥₂ 𝐵)

subsetIsPostable : ∀ {𝑓 𝑓′} → 𝑓 ⊆ 𝑓′ → Postable 𝑓′ → Postable 𝑓
subsetIsPostable {𝑓} {𝑓′} 𝑓⊆𝑓′ postable𝑓′
  with (boundedPostLemma 𝑓⊆𝑓′ (postableBounded postable𝑓′))
... | 𝑓bound = boundedPostable 𝑓bound
