{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Pre (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

data Preable : NbhFinFun 𝐴 𝐵 → Set
pre : (𝑓 : NbhFinFun 𝐴 𝐵) → Preable 𝑓 → NbhSys.Nbh 𝐴

data Preable where
  pre-nil : Preable ∅
  pre-cons : ∀ {x y 𝑓} → (preable𝑓 : Preable 𝑓) →
             NbhSys.Con 𝐴 x (pre 𝑓 preable𝑓) → Preable (< x , y > ∷ 𝑓)

pre ∅ _ = NbhSys.⊥ 𝐴
pre (< x , y > ∷ 𝑓) (pre-cons preable𝑓 conxpre𝑓)
  = [ 𝐴 ] x ⊔ pre 𝑓 preable𝑓 [ conxpre𝑓 ]

BoundedPre : NbhFinFun 𝐴 𝐵 → Set
BoundedPre 𝑓
  = Σ (NbhSys.Nbh 𝐴) λ max → ∀ {x y} → < x , y > ∈ 𝑓 → [ 𝐴 ] x ⊑ max

boundedPreLemma : 𝑓 ⊆ 𝑓′ → BoundedPre 𝑓′ → BoundedPre 𝑓
boundedPreLemma 𝑓⊆𝑓′ boundedPre𝑓′
  = (fst boundedPre𝑓′) , λ xy∈𝑓 → snd boundedPre𝑓′ (𝑓⊆𝑓′ _ xy∈𝑓)

boundedPreLemmaEq : (𝑓⊆𝑓″ : 𝑓 ⊆ 𝑓″) → (𝑓′⊆𝑓″ : 𝑓′ ⊆ 𝑓″) →
                    (bp𝑓″ : BoundedPre 𝑓″) →
                    (fst (boundedPreLemma 𝑓⊆𝑓″ bp𝑓″)) ≡ (fst (boundedPreLemma 𝑓′⊆𝑓″ bp𝑓″))
boundedPreLemmaEq _ _ _ = refl

preableBounded' : (preable𝑓 : Preable 𝑓) →
                  ∀ {x′ y′} → < x′ , y′ > ∈ 𝑓 →
                  [ 𝐴 ] x′ ⊑ (pre 𝑓 preable𝑓)
preableBounded' {< x , y > ∷ 𝑓} (pre-cons preable𝑓 conxpre𝑓) here
  = NbhSys.⊑-⊔-fst 𝐴 conxpre𝑓
preableBounded' {< x , y > ∷ 𝑓} (pre-cons preable𝑓 conxpre𝑓) (there x′y′∈𝑓)
  = NbhSys.⊑-trans 𝐴 (preableBounded' preable𝑓 x′y′∈𝑓) (NbhSys.⊑-⊔-snd 𝐴 conxpre𝑓)

preableBounded : Preable 𝑓 → BoundedPre 𝑓
preableBounded pre-nil = (NbhSys.⊥ 𝐴) , xy∈∅-abs
preableBounded {< x , y > ∷ 𝑓′} (pre-cons preable𝑓′ conxpre𝑓′)
  = [ 𝐴 ] x ⊔ pre 𝑓′ preable𝑓′ [ conxpre𝑓′ ] ,
    preableBounded' (pre-cons preable𝑓′ conxpre𝑓′)
  where 𝑓′bound = preableBounded preable𝑓′

preableLemma : (preable𝑓 : Preable 𝑓) →
               (boundedPre𝑓 : BoundedPre 𝑓) →
               [ 𝐴 ] (pre 𝑓 preable𝑓) ⊑ (fst boundedPre𝑓)
preableLemma {∅} _ _ = NbhSys.⊑-⊥ 𝐴
preableLemma {< x , y > ∷ 𝑓} (pre-cons preable𝑓 conxpre𝑓) boundedPrexy𝑓
  = NbhSys.⊑-⊔ 𝐴 ((snd boundedPrexy𝑓) here)
    (preableLemma preable𝑓 (boundedPreLemma (⊆-lemma₃ < x , y >) boundedPrexy𝑓))
    conxpre𝑓

preableProofIrr : (preable𝑓₁ preable𝑓₂ : Preable 𝑓) →
                  [ 𝐴 ] (pre 𝑓 preable𝑓₁) ⊑ (pre 𝑓 preable𝑓₂)
preableProofIrr {∅} pre-nil pre-nil = NbhSys.⊑-refl 𝐴
preableProofIrr {< x , y > ∷ 𝑓} (pre-cons preable𝑓₁ conxpre𝑓₁)
  (pre-cons preable𝑓₂ conxpre𝑓₂)
  = ⊑-⊔-lemma₃ 𝐴 _ _ (NbhSys.⊑-refl 𝐴) (preableProofIrr preable𝑓₁ preable𝑓₂)

preLemma''' : (bound𝑓 : BoundedPre 𝑓) → (bound𝑓′ : BoundedPre 𝑓′) →
              (preable𝑓 : Preable 𝑓) → (preable𝑓′ : Preable 𝑓′) →
              fst bound𝑓 ≡ fst bound𝑓′ →
              NbhSys.Con 𝐴 (pre 𝑓 preable𝑓) (pre 𝑓′ preable𝑓′)
preLemma''' {𝑓} {𝑓′} (_ , snd₁) bound𝑓′ preable𝑓 preable𝑓′ refl
  = NbhSys.Con-⊔ 𝐴 (preableLemma preable𝑓 (fst bound𝑓′ , snd₁))
    (preableLemma preable𝑓′ bound𝑓′)

preLemma₁'' : (preable𝑓 : Preable 𝑓) → (preable𝑓′ : Preable 𝑓′) →
              (preable∪ : Preable (𝑓 ∪ 𝑓′)) →
              NbhSys.Con 𝐴 (pre 𝑓 preable𝑓) (pre 𝑓′ preable𝑓′)
preLemma₁'' {𝑓} {𝑓′} preable𝑓 preable𝑓′ preable∪
  = preLemma''' boundedPre𝑓 boundedPre𝑓′ preable𝑓 preable𝑓′ sameBound
    where boundedPre𝑓 = boundedPreLemma ∪-lemma₃ (preableBounded preable∪)
          boundedPre𝑓′ = boundedPreLemma ∪-lemma₄ (preableBounded preable∪)
          boundedPre𝑓″ = preableBounded preable∪
          sameBound = boundedPreLemmaEq {𝑓 = 𝑓} {𝑓′ = 𝑓′} ∪-lemma₃ ∪-lemma₄ boundedPre𝑓″

preLemma₁' : ∀ x → (preable𝑓 : Preable 𝑓) → (preable𝑓′ : Preable 𝑓′) →
             (con₁ : NbhSys.Con 𝐴 x (pre 𝑓 preable𝑓)) →
             (con₂ : NbhSys.Con 𝐴 (pre 𝑓 preable𝑓) (pre 𝑓′ preable𝑓′)) →
             NbhSys.Con 𝐴 ([ 𝐴 ] x ⊔ pre 𝑓 preable𝑓 [ con₁ ]) (pre 𝑓′ preable𝑓′) →
             NbhSys.Con 𝐴 x ([ 𝐴 ] (pre 𝑓 preable𝑓) ⊔ (pre 𝑓′ preable𝑓′) [ con₂ ])
preLemma₁' {𝑓} {𝑓′} x preable𝑓 preable𝑓′ con₁ con₂ con₃
  = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-fst 𝐴 con₁) (NbhSys.⊑-⊔-fst 𝐴 con₃))
    (⊑-⊔-lemma₃ 𝐴 _ _ (NbhSys.⊑-⊔-snd 𝐴 _) (NbhSys.⊑-refl 𝐴))

preLemma₁ : (preable𝑓 : Preable 𝑓) → (preable𝑓′ : Preable 𝑓′) →
            (preable∪ : Preable (𝑓 ∪ 𝑓′)) →
            (conpre : NbhSys.Con 𝐴 (pre 𝑓 preable𝑓) (pre 𝑓′ preable𝑓′)) →
            [ 𝐴 ] (pre (𝑓 ∪ 𝑓′) preable∪) ⊑
            ([ 𝐴 ] (pre 𝑓 preable𝑓) ⊔ (pre 𝑓′ preable𝑓′) [ conpre ])
preLemma₁ {∅} {𝑓′} pre-nil _ _ _
  = ⊑-⊔-lemma₅ 𝐴 (preableProofIrr {𝑓 = 𝑓′} _ _) _
preLemma₁ {< x , y > ∷ 𝑓} {𝑓′} (pre-cons preable𝑓 conxpre𝑓) preable𝑓′
  (pre-cons preable∪ conxpre∪) conpre₁
  = NbhSys.⊑-trans 𝐴 (⊑-⊔-lemma₃ 𝐴 _ conxpre⊔ (NbhSys.⊑-refl 𝐴)
    (preLemma₁ {𝑓} {𝑓′} _ _ preable∪ conpre₂))
    (⊔-ass₂ 𝐴 _ conpre₂ conxpre⊔ _ (NbhSys.⊑-refl 𝐴))
  where conpre₂ = preLemma₁'' preable𝑓 preable𝑓′ preable∪
        conxpre⊔ = preLemma₁' x preable𝑓 preable𝑓′ conxpre𝑓 conpre₂ conpre₁

preUnionLemma' : ∀ {max} → (preable𝑓 : Preable 𝑓) →
                 (preable𝑓′ : Preable 𝑓′) → (preable∪ : Preable (𝑓 ∪ 𝑓′)) →
                 [ 𝐴 ] (pre 𝑓 preable𝑓) ⊑ max → [ 𝐴 ] (pre 𝑓′ preable𝑓′) ⊑ max →
                 [ 𝐴 ] (pre (𝑓 ∪ 𝑓′) preable∪) ⊑ max
preUnionLemma' {∅} {𝑓′} preable𝑓 preable𝑓′ preable∪ pre𝑓⊑max pre𝑓′⊑max
  = NbhSys.⊑-trans 𝐴 (preableProofIrr preable∪ preable𝑓′) pre𝑓′⊑max
preUnionLemma' {< x , y > ∷ 𝑓} (pre-cons preable𝑓 conxpre𝑓) preable𝑓′
  (pre-cons preable∪ conxpre∪) prexy𝑓⊑max pre𝑓′⊑max
  = NbhSys.⊑-⊔ 𝐴 x⊑max rec conxpre∪
  where pre𝑓⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-snd 𝐴 conxpre𝑓) prexy𝑓⊑max
        rec = preUnionLemma' preable𝑓 preable𝑓′ preable∪ pre𝑓⊑max pre𝑓′⊑max
        x⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-fst 𝐴 conxpre𝑓) prexy𝑓⊑max

preUnionLemma : ∀ {max} → (preable𝑓 : Preable 𝑓) →
                (preable𝑓′ : Preable 𝑓′) → [ 𝐴 ] (pre 𝑓 preable𝑓) ⊑ max →
                [ 𝐴 ] (pre 𝑓′ preable𝑓′) ⊑ max → Preable (𝑓 ∪ 𝑓′)
preUnionLemma {∅} _ preable𝑓′ _ _ = preable𝑓′
preUnionLemma {< x , y > ∷ 𝑓} (pre-cons preable𝑓 conxpre𝑓) preable𝑓′ pre𝑓⊑x pre𝑓′⊑x
  = pre-cons rec (NbhSys.Con-⊔ 𝐴 x⊑max pre∪⊑max)
  where pre𝑓⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-snd 𝐴 conxpre𝑓) pre𝑓⊑x
        rec = preUnionLemma preable𝑓 preable𝑓′ pre𝑓⊑max pre𝑓′⊑x
        x⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-fst 𝐴 conxpre𝑓) pre𝑓⊑x
        pre∪⊑max = preUnionLemma' preable𝑓 preable𝑓′ rec pre𝑓⊑max pre𝑓′⊑x

singletonIsPreable : ∀ {x y} → Preable (< x , y > ∷ ∅)
singletonIsPreable = pre-cons pre-nil (con⊥₂ 𝐴)
