{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.AxiomProofs
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

open import Agda.Builtin.Sigma

one : {x : NbhSys.Nbh 𝐴} → ∀ {y 𝑓 𝑓′ sub} →
      ∀ postable𝑓 postable𝑓′ postable∪ →
      [ 𝐵 ] y ⊑ post 𝑓 postable𝑓 →
      (∀ {x′ y′} → < x′ , y′ > ∈ sub → [ 𝐵 ] y′ ⊑ post 𝑓′ postable𝑓′) →
      ∀ {x′ y′} → < x′ , y′ > ∈ (< x , y > ∷ sub) →
      [ 𝐵 ] y′ ⊑ post (𝑓 ∪ 𝑓′) postable∪
one postable𝑓 _ postable∪ y⊑post𝑓 _ here
  = NbhSys.⊑-trans 𝐵 y⊑post𝑓 post𝑓⊑post∪
  where post𝑓⊑post∪ = post⊆-lemma₁ {postable𝑓 = postable𝑓} {postable∪}
one {𝑓′ = 𝑓′} _ postable𝑓′ postable∪ _ p (there x′y′∈sub)
  = NbhSys.⊑-trans 𝐵 (p x′y′∈sub)
    {!!} -- (post⊆-lemma {postable𝑓 = postable𝑓′} {postable∪} ∪-lemma₇)

record ⊑ₑ-proof₂ (𝑓 : NbhFinFun 𝐴 𝐵) (isCon : ConFinFun 𝑓)
                 (𝑓′ : NbhFinFun 𝐴 𝐵) (preable𝑓′ : Preable 𝑓′) :
                 Set where
  field
    sub : NbhFinFun 𝐴 𝐵
    sub⊆𝑓 : sub ⊆ 𝑓
    preablesub : Preable sub
    postablesub : Postable sub
    ybound : ∀ {x y} → < x , y > ∈ 𝑓′ → [ 𝐵 ] y ⊑ (post sub postablesub)
    pre⊑pre𝑓′ : [ 𝐴 ] (pre sub preablesub) ⊑ (pre 𝑓′ preable𝑓′)

Con-⊔ₑ' : ∀ {𝑓 𝑓′ 𝑓″ sub con𝑓 con𝑓′ con𝑓″} →
          (𝐹 𝑓 con𝑓) ⊑ₑ (𝐹 𝑓″ con𝑓″) → (𝐹 𝑓′ con𝑓′) ⊑ₑ (𝐹 𝑓″ con𝑓″) →
          sub ⊆ (𝑓 ∪ 𝑓′) → (preable : Preable sub) →
          ⊑ₑ-proof₂ 𝑓″ con𝑓″ sub preable
Con-⊔ₑ' {sub = ∅} _ _ _ _
  = record
      { sub = ∅
      ; sub⊆𝑓 = ∅-isSubset
      ; preablesub = pre-nil
      ; postablesub = post-nil
      ; ybound = xy∈∅-abs
      ; pre⊑pre𝑓′ = NbhSys.⊑-⊥ 𝐴
      }
Con-⊔ₑ' {𝑓 = 𝑓} {sub = < x , y > ∷ sub} _ _ sub⊆𝑓∪𝑓′ _
  with (∪-lemma₂ {𝑓 = 𝑓} < x , y > (sub⊆𝑓∪𝑓′ < x , y > here))
Con-⊔ₑ' {sub = < x , y > ∷ sub} (⊑ₑ-intro₂ _ _ _ _ p) _ _ _
  | inl xy∈𝑓 with (p x y xy∈𝑓)
Con-⊔ₑ' {sub = < x , y > ∷ sub} {con𝑓″ = cff p} 𝑓⊑𝑓″ 𝑓′⊑𝑓″ sub⊆𝑓∪𝑓′ preable
  | inl xy∈𝑓
  | record { sub = sub″
           ; sub⊆𝑓 = sub″⊆𝑓″
           ; preablesub = preablesub″
           ; postablesub = postablesub″
           ; y⊑post = y⊑post″
           ; pre⊑x = pre″⊑x
           }
  = record
      { sub = sub″ ∪ recsub
      ; sub⊆𝑓 = ∪⊆𝑓″
      ; preablesub = preable∪
      ; postablesub = postable∪
      ; ybound = one postablesub″ recpostablesub postable∪ y⊑post″ recybound
      ; pre⊑pre𝑓′ = {!!}
      }
      -- pre (sub″ ∪ recsub) ⊑ (pre sub″) ⊔ (pre recsub)
      -- pre sub″ ⊑ x ⊑ pre (< x , y > ∷ sub)
      -- pre recsub ⊑ pre sub ⊑ (< x , y > ∷ sub)
  where rec = Con-⊔ₑ' {sub = sub} 𝑓⊑𝑓″ 𝑓′⊑𝑓″
              (⊆-lemma₂ < x , y > sub⊆𝑓∪𝑓′)
              (subsetIsPreable (⊆-lemma₃ < x , y >) preable)
        recsub = ⊑ₑ-proof₂.sub rec
        recsub⊆𝑓″ = ⊑ₑ-proof₂.sub⊆𝑓 rec
        recpostablesub = ⊑ₑ-proof₂.postablesub rec
        recpreablesub = ⊑ₑ-proof₂.preablesub rec
        recybound = ⊑ₑ-proof₂.ybound rec
        recpre⊑pre𝑓′ = ⊑ₑ-proof₂.pre⊑pre𝑓′ rec
        sub″⊑prexysub = NbhSys.⊑-trans 𝐴 pre″⊑x {!!}
        recsub⊑prexysub = NbhSys.⊑-trans 𝐴 recpre⊑pre𝑓′ {!!}
        preable∪ = preUnionLemma {max = pre (< x , y > ∷ sub) preable} preablesub″ recpreablesub sub″⊑prexysub recsub⊑prexysub
        ∪⊆𝑓″ = ∪-lemma₁ sub″⊆𝑓″ recsub⊆𝑓″
        postable∪ = p ∪⊆𝑓″ preable∪
Con-⊔ₑ' {sub = < x , y > ∷ sub} (⊑ₑ-intro₂ _ _ _ _ p) _ _ _
  | inr xy∈𝑓′ = {!!}

Con-⊔ₑ : ∀ {x y z} → x ⊑ₑ z → y ⊑ₑ z → ArrCon x y
Con-⊔ₑ {⊥ₑ} {y} _ _ = conₑ-⊥₂
Con-⊔ₑ {𝐹 𝑓 _} {⊥ₑ} _ _ = conₑ-⊥₁
Con-⊔ₑ {𝐹 𝑓 _} {𝐹 𝑓′ _} {⊥ₑ} () _
Con-⊔ₑ {𝐹 𝑓 con𝑓} {𝐹 𝑓′ con𝑓′} {𝐹 𝑓″ con𝑓″} 𝑓⊑𝑓″ 𝑓′⊑𝑓″
  = ArrCon.con-∪ _ _ (cff λ {𝑓′ = sub} sub⊆𝑓∪𝑓′ preablesub →
    boundedPostable ({!!} , {!!}))

⊑ₑ-refl : ∀ {x} → x ⊑ₑ x
⊑ₑ-refl {⊥ₑ} = ⊑ₑ-intro₁
⊑ₑ-refl {𝐹 𝑓 con𝑓} = ⊑ₑ-intro₂ 𝑓 𝑓 con𝑓 con𝑓 λ x y xy∈𝑓 →
  record
    { sub = < x , y > ∷ ∅
    ; sub⊆𝑓 = ⊆-lemma₄ < x , y > xy∈𝑓 ∅-isSubset
    ; preablesub = singletonIsPreable
    ; postablesub = singletonIsPostable
    ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵) (con⊥₂ 𝐵)
    ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴) (con⊥₂ 𝐴)
    }

⊑ₑ-⊥ₑ : ∀ {x} → ⊥ₑ ⊑ₑ x
⊑ₑ-⊥ₑ = ⊑ₑ-intro₁

⊑ₑ-⊔ₑ' : ∀ {𝑓 𝑓′ 𝑓″ con𝑓 con𝑓′ con𝑓″} →
         𝐹 𝑓′ con𝑓′ ⊑ₑ 𝐹 𝑓 con𝑓 → 𝐹 𝑓″ con𝑓″ ⊑ₑ 𝐹 𝑓 con𝑓 →
         ∀ x y → < x , y > ∈ (𝑓′ ∪ 𝑓″) →
         ⊑ₑ-proof 𝑓 con𝑓 x y
⊑ₑ-⊔ₑ' {𝑓′ = 𝑓′} _ _ x y xy∈∪
  with (∪-lemma₂  {𝑓 = 𝑓′} < x , y > xy∈∪)
⊑ₑ-⊔ₑ' (⊑ₑ-intro₂ _ _ _ _ p) _ x y xy∈∪ | inl xy∈𝑓′
  = p x y xy∈𝑓′
⊑ₑ-⊔ₑ' _ (⊑ₑ-intro₂ _ _ _ _ p) x y xy∈∪ | inr xy∈𝑓″
  = p x y xy∈𝑓″

⊑ₑ-⊔ₑ : ∀ {x y z} → y ⊑ₑ x → z ⊑ₑ x → (conyz : ArrCon y z) →
        (y ⊔ₑ z [ conyz ]) ⊑ₑ x
⊑ₑ-⊔ₑ {y = ⊥ₑ} {⊥ₑ} _ _ _ = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ {y = 𝐹 _ _} {⊥ₑ} y⊑x _ _ = y⊑x
⊑ₑ-⊔ₑ {y = ⊥ₑ} {𝐹 _ _} _ z⊑x _ = z⊑x
⊑ₑ-⊔ₑ {x = ArrNbh.𝐹 𝑓 _} {ArrNbh.𝐹 𝑓′ _} {ArrNbh.𝐹 𝑓″ _} y⊑x z⊑x
  (ArrCon.con-∪ _ _ _)
  = ⊑ₑ-intro₂ (𝑓′ ∪ 𝑓″) 𝑓 _ _ (⊑ₑ-⊔ₑ' y⊑x z⊑x)

⊑ₑ-⊔ₑ-fst : ∀ {x y} → (conxy : ArrCon x y) → x ⊑ₑ (x ⊔ₑ y [ conxy ])
⊑ₑ-⊔ₑ-fst {⊥ₑ} _ = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ-fst {𝐹 𝑓 _} {⊥ₑ} _ = ⊑ₑ-refl
⊑ₑ-⊔ₑ-fst {𝐹 𝑓 _} {𝐹 𝑓′ _} (ArrCon.con-∪ _ _ _)
  = ⊑ₑ-intro₂ 𝑓 (𝑓 ∪ 𝑓′) _ _ λ x y xy∈𝑓 →
  record
    { sub = < x , y > ∷ ∅
    ; sub⊆𝑓 = ⊆-lemma₄ < x , y > (∪-lemma₃ < x , y > xy∈𝑓)
              ∅-isSubset
    ; preablesub = singletonIsPreable
    ; postablesub = singletonIsPostable
    ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵) (con⊥₂ 𝐵)
    ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
              (con⊥₂ 𝐴)
    }

⊑ₑ-⊔ₑ-snd : ∀ {x y} → (conxy : ArrCon x y) → y ⊑ₑ (x ⊔ₑ y [ conxy ])
⊑ₑ-⊔ₑ-snd {y = ⊥ₑ} _ = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ-snd {⊥ₑ} {𝐹 𝑓 _} _ = ⊑ₑ-refl
⊑ₑ-⊔ₑ-snd {𝐹 𝑓 _} {𝐹 𝑓′ _} (ArrCon.con-∪ _ _ _)
  = ⊑ₑ-intro₂ 𝑓′ (𝑓 ∪ 𝑓′) _ _ λ x y xy∈𝑓′ →
  record
    { sub = < x , y > ∷ ∅
    ; sub⊆𝑓 = ⊆-lemma₄ < x , y > (∪-lemma₄ < x , y > xy∈𝑓′)
              ∅-isSubset
    ; preablesub = singletonIsPreable
    ; postablesub = singletonIsPostable
    ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵) (con⊥₂ 𝐵)
    ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
              (con⊥₂ 𝐴)
    }
