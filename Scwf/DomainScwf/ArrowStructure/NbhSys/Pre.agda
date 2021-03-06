{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Pre
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

data Preable : NbhFinFun 𝐴 𝐵 → Set
pre : (𝑓 : NbhFinFun 𝐴 𝐵) → Preable 𝑓 → NbhSys.Nbh 𝐴

data Preable where
  pre-nil : Preable ∅
  pre-cons : ∀ {x y 𝑓} → (preable𝑓 : Preable 𝑓) →
             NbhSys.Con 𝐴 x (pre 𝑓 preable𝑓) → Preable ((x , y) ∷ 𝑓)

pre ∅ _ = NbhSys.⊥ 𝐴
pre ((x , y) ∷ 𝑓) (pre-cons preable𝑓 conxpre𝑓)
  = [ 𝐴 ] x ⊔ pre 𝑓 preable𝑓 [ conxpre𝑓 ]

preableProofIrr : (preable𝑓₁ preable𝑓₂ : Preable 𝑓) →
                  [ 𝐴 ] (pre 𝑓 preable𝑓₁) ⊑ (pre 𝑓 preable𝑓₂)
preableProofIrr {∅} pre-nil pre-nil = NbhSys.⊑-refl 𝐴
preableProofIrr {(x , y) ∷ 𝑓} (pre-cons preable𝑓₁ conxpre𝑓₁)
  (pre-cons preable𝑓₂ conxpre𝑓₂)
  = ⊑-⊔-lemma₃ 𝐴 _ _ (NbhSys.⊑-refl 𝐴)
    (preableProofIrr preable𝑓₁ preable𝑓₂)

preLemma₁ : ∀ {𝑓 𝑓′ preable𝑓 preable∪} →
            [ 𝐴 ] pre 𝑓 preable𝑓 ⊑ pre (𝑓 ∪ 𝑓′) preable∪
preLemma₁ {preable𝑓 = pre-nil} = NbhSys.⊑-⊥ 𝐴
preLemma₁ {𝑓 = _ ∷ 𝑓} {preable𝑓 = pre-cons preable𝑓 conxpre𝑓}
  {pre-cons preable𝑓∪𝑓′ conxpre∪}
  = ⊑-⊔-lemma₃ 𝐴 _ _ (NbhSys.⊑-refl 𝐴) rec
  where rec = preLemma₁ {𝑓 = 𝑓} {preable𝑓 = preable𝑓}

preLemma₂ : ∀ {𝑓 𝑓′ preable𝑓′ preable∪} →
            [ 𝐴 ] pre 𝑓′ preable𝑓′ ⊑ pre (𝑓 ∪ 𝑓′) preable∪
preLemma₂ {𝑓 = _} {∅} = NbhSys.⊑-⊥ 𝐴
preLemma₂ {𝑓 = ∅} {_ ∷ _} {preable𝑓′}
  = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-refl 𝐴)
    (preableProofIrr preable𝑓′ _)
preLemma₂ {𝑓 = (x , y) ∷ 𝑓} {(x′ , y′) ∷ 𝑓′}
  {pre-cons preable𝑓′tail conxpre𝑓′tail}
  {pre-cons preable∪tail x′con∪tail}
  = ⊑-⊔-lemma₅ 𝐴 rec x′con∪tail
  where preable𝑓′ = pre-cons preable𝑓′tail conxpre𝑓′tail
        rec = preLemma₂ {𝑓 = 𝑓} {𝑓′ = (x′ , y′) ∷ 𝑓′}
              {preable𝑓′ = preable𝑓′}

preLemma₃'' : (preable𝑓 : Preable 𝑓) → (preable𝑓′ : Preable 𝑓′) →
              (preable∪ : Preable (𝑓 ∪ 𝑓′)) →
              NbhSys.Con 𝐴 (pre 𝑓 preable𝑓) (pre 𝑓′ preable𝑓′)
preLemma₃'' {𝑓} {𝑓′} preable𝑓 preable𝑓′ preable∪
  = NbhSys.Con-⊔ 𝐴 pre𝑓⊑pre∪ pre𝑓′⊑pre∪
  where pre𝑓⊑pre∪ = preLemma₁ {𝑓 = 𝑓} {preable∪ = preable∪}
        pre𝑓′⊑pre∪ = preLemma₂ {𝑓′ = 𝑓′} {preable∪ = preable∪}

preLemma₃' : ∀ x → (preable𝑓 : Preable 𝑓) → (preable𝑓′ : Preable 𝑓′) →
             (con₁ : NbhSys.Con 𝐴 x (pre 𝑓 preable𝑓)) →
             (con₂ : NbhSys.Con 𝐴 (pre 𝑓 preable𝑓) (pre 𝑓′ preable𝑓′)) →
             NbhSys.Con 𝐴 ([ 𝐴 ] x ⊔ pre 𝑓 preable𝑓 [ con₁ ])
               (pre 𝑓′ preable𝑓′) →
             NbhSys.Con 𝐴 x ([ 𝐴 ] (pre 𝑓 preable𝑓) ⊔
               (pre 𝑓′ preable𝑓′) [ con₂ ])
preLemma₃' {𝑓} {𝑓′} x preable𝑓 preable𝑓′ con₁ con₂ con₃
  = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-fst 𝐴 con₁)
    (NbhSys.⊑-⊔-fst 𝐴 con₃))
    (⊑-⊔-lemma₃ 𝐴 _ _ (NbhSys.⊑-⊔-snd 𝐴 _) (NbhSys.⊑-refl 𝐴))

preLemma₃ : (preable𝑓 : Preable 𝑓) → (preable𝑓′ : Preable 𝑓′) →
            (preable∪ : Preable (𝑓 ∪ 𝑓′)) →
            (conpre : NbhSys.Con 𝐴 (pre 𝑓 preable𝑓) (pre 𝑓′ preable𝑓′)) →
            [ 𝐴 ] (pre (𝑓 ∪ 𝑓′) preable∪) ⊑
            ([ 𝐴 ] (pre 𝑓 preable𝑓) ⊔ (pre 𝑓′ preable𝑓′) [ conpre ])
preLemma₃ {∅} {𝑓′} pre-nil _ _ _
  = ⊑-⊔-lemma₅ 𝐴 (preableProofIrr {𝑓 = 𝑓′} _ _) _
preLemma₃ {(x , y) ∷ 𝑓} {𝑓′} (pre-cons preable𝑓 conxpre𝑓) preable𝑓′
  (pre-cons preable∪ conxpre∪) conpre₁
  = NbhSys.⊑-trans 𝐴 (⊑-⊔-lemma₃ 𝐴 _ conxpre⊔ (NbhSys.⊑-refl 𝐴)
    (preLemma₃ {𝑓} {𝑓′} _ _ preable∪ conpre₂))
    (⊔-ass₂ 𝐴 _ conpre₂ conxpre⊔ _ (NbhSys.⊑-refl 𝐴))
  where conpre₂ = preLemma₃'' preable𝑓 preable𝑓′ preable∪
        conxpre⊔ = preLemma₃' x preable𝑓 preable𝑓′ conxpre𝑓 conpre₂ conpre₁

preUnionLemma' : ∀ {max} → (preable𝑓 : Preable 𝑓) →
                 (preable𝑓′ : Preable 𝑓′) →
                 (preable∪ : Preable (𝑓 ∪ 𝑓′)) →
                 [ 𝐴 ] (pre 𝑓 preable𝑓) ⊑ max →
                 [ 𝐴 ] (pre 𝑓′ preable𝑓′) ⊑ max →
                 [ 𝐴 ] (pre (𝑓 ∪ 𝑓′) preable∪) ⊑ max
preUnionLemma' {∅} {𝑓′} preable𝑓 preable𝑓′ preable∪ pre𝑓⊑max pre𝑓′⊑max
  = NbhSys.⊑-trans 𝐴 (preableProofIrr preable∪ preable𝑓′) pre𝑓′⊑max
preUnionLemma' {(x , y) ∷ 𝑓} (pre-cons preable𝑓 conxpre𝑓) preable𝑓′
  (pre-cons preable∪ conxpre∪) prexy𝑓⊑max pre𝑓′⊑max
  = NbhSys.⊑-⊔ 𝐴 x⊑max rec conxpre∪
  where pre𝑓⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-snd 𝐴 conxpre𝑓)
                   prexy𝑓⊑max
        rec = preUnionLemma' preable𝑓 preable𝑓′ preable∪ pre𝑓⊑max
              pre𝑓′⊑max
        x⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-fst 𝐴 conxpre𝑓)
                prexy𝑓⊑max

preUnionLemma : ∀ {max} → (preable𝑓 : Preable 𝑓) →
                (preable𝑓′ : Preable 𝑓′) →
                [ 𝐴 ] (pre 𝑓 preable𝑓) ⊑ max →
                [ 𝐴 ] (pre 𝑓′ preable𝑓′) ⊑ max → Preable (𝑓 ∪ 𝑓′)
preUnionLemma {∅} _ preable𝑓′ _ _ = preable𝑓′
preUnionLemma {(x , y) ∷ 𝑓} (pre-cons preable𝑓 conxpre𝑓)
  preable𝑓′ pre𝑓⊑x pre𝑓′⊑x
  = pre-cons rec (NbhSys.Con-⊔ 𝐴 x⊑max pre∪⊑max)
  where pre𝑓⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-snd 𝐴 conxpre𝑓)
                   pre𝑓⊑x
        rec = preUnionLemma preable𝑓 preable𝑓′ pre𝑓⊑max pre𝑓′⊑x
        x⊑max = NbhSys.⊑-trans 𝐴 (NbhSys.⊑-⊔-fst 𝐴 conxpre𝑓) pre𝑓⊑x
        pre∪⊑max = preUnionLemma' preable𝑓 preable𝑓′ rec pre𝑓⊑max
                   pre𝑓′⊑x

singletonIsPreable : ∀ {x y} → Preable ((x , y) ∷ ∅)
singletonIsPreable = pre-cons pre-nil (con⊥₂ 𝐴)
