{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Consistency
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

yboundlemma : {x : NbhSys.Nbh 𝐴} → ∀ {y sub} →
      ∀ postable𝑓 postable𝑓′ postable∪ →
      [ 𝐵 ] y ⊑ post 𝑓 postable𝑓 →
      (∀ {x′ y′} → < x′ , y′ > ∈ sub → [ 𝐵 ] y′ ⊑ post 𝑓′ postable𝑓′) →
      ∀ {x′ y′} → < x′ , y′ > ∈ (< x , y > ∷ sub) →
      [ 𝐵 ] y′ ⊑ post (𝑓 ∪ 𝑓′) postable∪
yboundlemma {𝑓 = 𝑓} {𝑓′} postable𝑓 _ postable∪ y⊑post𝑓 _ here
  = NbhSys.⊑-trans 𝐵 y⊑post𝑓 post𝑓⊑post∪
  where post𝑓⊑post∪ = postLemma₁ {𝑓 = 𝑓} {𝑓′}
yboundlemma {𝑓 = 𝑓} {𝑓′} _ postable𝑓′ postable∪ _ p (there x′y′∈sub)
  = NbhSys.⊑-trans 𝐵 (p x′y′∈sub) post𝑓′⊑post∪
  where post𝑓′⊑post∪ = postLemma₂ {𝑓 = 𝑓} {𝑓′}

record ⊑ₑ-proof₃ (𝑓 : NbhFinFun 𝐴 𝐵) (isCon : ConFinFun 𝑓)
                 (𝑓′ : NbhFinFun 𝐴 𝐵) (preable𝑓′ : Preable 𝑓′) :
                 Set where
  field
    sub : NbhFinFun 𝐴 𝐵
    sub⊆𝑓 : sub ⊆ 𝑓
    preablesub : Preable sub
    postablesub : Postable sub
    ybound : ∀ {x y} → < x , y > ∈ 𝑓′ → [ 𝐵 ] y ⊑ (post sub postablesub)
    pre⊑pre𝑓′ : [ 𝐴 ] (pre sub preablesub) ⊑ (pre 𝑓′ preable𝑓′)

Con-⊔ₑ'' : ∀ {sub con𝑓 con𝑓′ con𝑓″} →
           (𝐹 𝑓 con𝑓) ⊑ₑ (𝐹 𝑓″ con𝑓″) →
           (𝐹 𝑓′ con𝑓′) ⊑ₑ (𝐹 𝑓″ con𝑓″) →
           sub ⊆ (𝑓 ∪ 𝑓′) → (preable : Preable sub) →
           ⊑ₑ-proof₃ 𝑓″ con𝑓″ sub preable
Con-⊔ₑ'' {sub = ∅} _ _ _ _
  = record
      { sub = ∅
      ; sub⊆𝑓 = ∅-isSubset
      ; preablesub = pre-nil
      ; postablesub = post-nil
      ; ybound = xy∈∅-abs
      ; pre⊑pre𝑓′ = NbhSys.⊑-⊥ 𝐴
      }
Con-⊔ₑ'' {𝑓 = 𝑓} {sub = < x , y > ∷ sub} _ _ sub⊆𝑓∪𝑓′ _
  with (∪-lemma₂ {𝑓 = 𝑓} (sub⊆𝑓∪𝑓′ < x , y > here))
Con-⊔ₑ'' {sub = < x , y > ∷ sub} (⊑ₑ-intro₂ _ _ _ _ p) _ _ _
  | inl xy∈𝑓 with (p x y xy∈𝑓)
Con-⊔ₑ'' {sub = < x , y > ∷ sub} {con𝑓″ = cff p} 𝑓⊑𝑓″ 𝑓′⊑𝑓″
  sub⊆𝑓∪𝑓′ (pre-cons preablesub conxpresub)
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
      ; ybound = yboundlemma postablesub″ recpostablesub postable∪
                 y⊑post″ recybound
      ; pre⊑pre𝑓′ = NbhSys.⊑-trans 𝐴 (preLemma₃ preablesub″ recpreablesub
                    preable∪ consub″recsub)
                    (⊑-⊔-lemma₃ 𝐴 consub″recsub conxpresub pre″⊑x
                    recpre⊑pre𝑓′)
      }
  where rec = Con-⊔ₑ'' 𝑓⊑𝑓″ 𝑓′⊑𝑓″ (⊆-lemma₂ sub⊆𝑓∪𝑓′)
              preablesub
        recsub = ⊑ₑ-proof₃.sub rec
        recsub⊆𝑓″ = ⊑ₑ-proof₃.sub⊆𝑓 rec
        recpostablesub = ⊑ₑ-proof₃.postablesub rec
        recpreablesub = ⊑ₑ-proof₃.preablesub rec
        recybound = ⊑ₑ-proof₃.ybound rec
        recpre⊑pre𝑓′ = ⊑ₑ-proof₃.pre⊑pre𝑓′ rec
        sub″⊑prexysub = NbhSys.⊑-trans 𝐴 pre″⊑x (NbhSys.⊑-⊔-fst 𝐴 conxpresub)
        recsub⊑prexysub = NbhSys.⊑-trans 𝐴 recpre⊑pre𝑓′ (NbhSys.⊑-⊔-snd 𝐴 _)
        preable∪ = preUnionLemma preablesub″ recpreablesub sub″⊑prexysub
                   recsub⊑prexysub
        ∪⊆𝑓″ = ∪-lemma₁ sub″⊆𝑓″ recsub⊆𝑓″
        postable∪ = p ∪⊆𝑓″ preable∪
        consub″recsub = NbhSys.Con-⊔ 𝐴 {z = pre (sub″ ∪ recsub) preable∪}
                        (preLemma₁ {preable𝑓 = preablesub″} {preable∪})
                        (preLemma₂ {preable𝑓′ = recpreablesub} {preable∪})
Con-⊔ₑ'' {sub = < x , y > ∷ sub} _ (⊑ₑ-intro₂ _ _ _ _ p) _ _
  | inr xy∈𝑓′ with (p x y xy∈𝑓′)
Con-⊔ₑ'' {sub = < x , y > ∷ sub} {con𝑓″ = cff p} 𝑓⊑𝑓″ 𝑓′⊑𝑓″
  sub⊆𝑓∪𝑓′ (pre-cons preablesub conxpresub)
  | inr xy∈𝑓′
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
      ; ybound = yboundlemma postablesub″ recpostablesub postable∪
                 y⊑post″ recybound
      ; pre⊑pre𝑓′ = NbhSys.⊑-trans 𝐴 (preLemma₃ preablesub″ recpreablesub
                    preable∪ consub″recsub)
                    (⊑-⊔-lemma₃ 𝐴 consub″recsub conxpresub pre″⊑x
                    recpre⊑pre𝑓′)
      }
  where rec = Con-⊔ₑ'' 𝑓⊑𝑓″ 𝑓′⊑𝑓″ (⊆-lemma₂ sub⊆𝑓∪𝑓′)
              preablesub
        recsub = ⊑ₑ-proof₃.sub rec
        recsub⊆𝑓″ = ⊑ₑ-proof₃.sub⊆𝑓 rec
        recpostablesub = ⊑ₑ-proof₃.postablesub rec
        recpreablesub = ⊑ₑ-proof₃.preablesub rec
        recybound = ⊑ₑ-proof₃.ybound rec
        recpre⊑pre𝑓′ = ⊑ₑ-proof₃.pre⊑pre𝑓′ rec
        sub″⊑prexysub = NbhSys.⊑-trans 𝐴 pre″⊑x (NbhSys.⊑-⊔-fst 𝐴 conxpresub)
        recsub⊑prexysub = NbhSys.⊑-trans 𝐴 recpre⊑pre𝑓′ (NbhSys.⊑-⊔-snd 𝐴 _)
        preable∪ = preUnionLemma preablesub″ recpreablesub sub″⊑prexysub
                   recsub⊑prexysub
        ∪⊆𝑓″ = ∪-lemma₁ sub″⊆𝑓″ recsub⊆𝑓″
        postable∪ = p ∪⊆𝑓″ preable∪
        consub″recsub = NbhSys.Con-⊔ 𝐴 {z = pre (sub″ ∪ recsub) preable∪}
                        (preLemma₁ {preable𝑓 = preablesub″} {preable∪})
                        (preLemma₂ {preable𝑓′ = recpreablesub} {preable∪})

Con-⊔ₑ' : ∀ {sub con𝑓 con𝑓′ con𝑓″} →
          (𝐹 𝑓 con𝑓) ⊑ₑ (𝐹 𝑓″ con𝑓″) →
          (𝐹 𝑓′ con𝑓′) ⊑ₑ (𝐹 𝑓″ con𝑓″) →
          sub ⊆ (𝑓 ∪ 𝑓′) → (preable : Preable sub) →
          Postable sub
Con-⊔ₑ' 𝑓⊑𝑓″ 𝑓′⊑𝑓″ sub⊆𝑓∪𝑓′ preablesub
  = boundedPostable ybound
  where proof = Con-⊔ₑ'' 𝑓⊑𝑓″ 𝑓′⊑𝑓″ sub⊆𝑓∪𝑓′ preablesub
        sub″ = ⊑ₑ-proof₃.sub proof
        ybound = ⊑ₑ-proof₃.ybound proof

Con-⊔ₑ : ∀ {x y z} → x ⊑ₑ z → y ⊑ₑ z → ArrCon x y
Con-⊔ₑ {⊥ₑ} {y} _ _ = conₑ-⊥₂
Con-⊔ₑ {𝐹 𝑓 _} {⊥ₑ} _ _ = conₑ-⊥₁
Con-⊔ₑ {𝐹 𝑓 _} {𝐹 𝑓′ _} {⊥ₑ} () _
Con-⊔ₑ {𝐹 𝑓 con𝑓} {𝐹 𝑓′ con𝑓′} {𝐹 𝑓″ con𝑓″} 𝑓⊑𝑓″ 𝑓′⊑𝑓″
  = ArrCon.con-∪ _ _ (cff λ {𝑓′ = sub} sub⊆𝑓∪𝑓′ preablesub →
    Con-⊔ₑ' 𝑓⊑𝑓″ 𝑓′⊑𝑓″ sub⊆𝑓∪𝑓′ preablesub)
