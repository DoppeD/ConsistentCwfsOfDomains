{-# OPTIONS --safe #-}

open import Base.Core

module PCF.DomainPCF.Functions.fix.Lemmata
  {𝐴 : Ty} where

open import Base.Core
open import Base.FinFun
open import Base.Variables hiding (𝐴)
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.fix.Relation 𝐴
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre (𝐴 ⇒ 𝐴) 𝐴
import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐴
  as Post𝐴
import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐴
  as Pre𝐴

↓closedLemma₁' : ∀ {x y x′ y′ conxy} →
                 [ 𝐴 ] x ⊑ x′ → [ 𝐴 ] y′ ⊑ y →
                 ∀ {x″ y″} → (x″ , y″) ∈ ((x′ , y′) ∷ ∅) →
                 ⊑ₑ-proof 𝐴 𝐴 ((x , y) ∷ ∅) conxy x″ y″
↓closedLemma₁' {x} {y} x⊑x′ y′⊑y here
  = record { sub = (x , y) ∷ ∅
           ; sub⊆𝑓 = ⊆-refl
           ; preablesub = Pre𝐴.singletonIsPreable
           ; postablesub = Post𝐴.singletonIsPostable
           ; y⊑post = ⊑-⊔-lemma₄ 𝐴 y′⊑y cony⊥
           ; pre⊑x = NbhSys.⊑-⊔ 𝐴 x⊑x′ (NbhSys.⊑-⊥ 𝐴) conx⊥
           }
  where cony⊥ = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴)
                (NbhSys.⊑-⊥ 𝐴)
        conx⊥ = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴)
                (NbhSys.⊑-⊥ 𝐴)

↓closedLemma₁ : ∀ {𝑓 𝑓′ x y x′ y′ conxy conx′y′} →
                [ 𝐴 ] x ⊑ x′ →  [ 𝐴 ] y′ ⊑ y →
                [ 𝐴 ⇒ 𝐴 ] 𝑓 ⊑ 𝑓′ →
                [ 𝐴 ⇒ 𝐴 ] (𝐹 ((x , y) ∷ ∅) conxy) ⊑ 𝑓 →
                [ 𝐴 ⇒ 𝐴 ] (𝐹 ((x′ , y′) ∷ ∅) conx′y′) ⊑ 𝑓′
↓closedLemma₁ x⊑x′ y′⊑y 𝑓⊑𝑓′ xy⊑𝑓
  = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) x′y′⊑xy xy⊑𝑓′
  where xy⊑𝑓′ = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) xy⊑𝑓 𝑓⊑𝑓′
        x′y′⊑xy = ⊑ₑ-intro₂ _ _ (↓closedLemma₁' x⊑x′ y′⊑y)

liftDerFrom⊥ : ∀ {𝑓 𝑓′ x} → [ 𝐴 ⇒ 𝐴 ] 𝑓 ⊑ 𝑓′ →
               derFrom⊥ 𝑓 x →
               derFrom⊥ 𝑓′ x
liftDerFrom⊥ _ (df⊥-intro₁ x⊑⊥) = df⊥-intro₁ x⊑⊥
liftDerFrom⊥ 𝑓⊑𝑓′ (df⊥-intro₂ df𝑓x′ xx′⊑𝑓)
  = df⊥-intro₂ df𝑓′x′ xx′⊑𝑓′
  where df𝑓′x′ = liftDerFrom⊥ 𝑓⊑𝑓′ df𝑓x′
        xx′⊑𝑓′ = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) xx′⊑𝑓 𝑓⊑𝑓′

liftDerFrom⊥₂ : ∀ {𝑓 𝑓′ x x′} → [ 𝐴 ⇒ 𝐴 ] 𝑓 ⊑ 𝑓′ →
                [ 𝐴 ] x′ ⊑ x →
                derFrom⊥ 𝑓 x →
                derFrom⊥ 𝑓′ x′
liftDerFrom⊥₂ 𝑓⊑𝑓′ _ df⊥𝑓x
  with (liftDerFrom⊥ 𝑓⊑𝑓′ df⊥𝑓x)
liftDerFrom⊥₂ _ x′⊑x _ | df⊥-intro₁ x⊑⊥
  = df⊥-intro₁ x′⊑⊥
  where x′⊑⊥ = NbhSys.⊑-trans 𝐴 x′⊑x x⊑⊥
liftDerFrom⊥₂ 𝑓⊑𝑓′ x′⊑x df⊥𝑓x
  | df⊥-intro₂ df⊥𝑓′y yx⊑𝑓′
  = df⊥-intro₂ df⊥𝑓′y xx′⊑𝑓′
  where 𝑓′⊑𝑓′ = NbhSys.⊑-refl (𝐴 ⇒ 𝐴)
        xx′⊑𝑓′ = ↓closedLemma₁ (NbhSys.⊑-refl 𝐴) x′⊑x 𝑓′⊑𝑓′ yx⊑𝑓′

↓closedLemma₂' : ∀ {x x′ y y′ conxy conx′y′ 𝑔} → ∀ cff𝑔 →
                 NbhSys.Con 𝐴 x x′ →
                 [ 𝐴 ⇒ 𝐴 ] (𝐹 ((x , y) ∷ ∅) conxy) ⊑ 𝐹 𝑔 cff𝑔 →
                 [ 𝐴 ⇒ 𝐴 ] (𝐹 ((x′ , y′) ∷ ∅) conx′y′) ⊑ 𝐹 𝑔 cff𝑔 →
                 NbhSys.Con 𝐴 y y′
↓closedLemma₂' (cff cff𝑔) conxx′ (⊑ₑ-intro₂ _ _ p₁)
  (⊑ₑ-intro₂ _ _ p₂)
  with (p₁ here) | (p₂ here)
... | record { sub = sub₁
             ; sub⊆𝑓 = sub⊆𝑓₁
             ; preablesub = preable₁
             ; postablesub = postable₁
             ; y⊑post = y⊑post₁
             ; pre⊑x = pre⊑x₁
             }
    | record { sub = sub₂
             ; sub⊆𝑓 = sub⊆𝑓₂
             ; preablesub = preable₂
             ; postablesub = postable₂
             ; y⊑post = y⊑post₂
             ; pre⊑x = pre⊑x₂
             }
  = NbhSys.Con-⊔ 𝐴 y⊑post∪ y′⊑post∪
  where x⊑x⊔x′ = NbhSys.⊑-⊔-fst 𝐴 conxx′
        x′⊑x⊔x′ = NbhSys.⊑-⊔-snd 𝐴 conxx′
        pre₁⊑x⊔x′ = NbhSys.⊑-trans 𝐴 pre⊑x₁ x⊑x⊔x′
        pre₂⊑x⊔x′ = NbhSys.⊑-trans 𝐴 pre⊑x₂ x′⊑x⊔x′
        preable∪ = Pre𝐴.preUnionLemma preable₁ preable₂
                   pre₁⊑x⊔x′ pre₂⊑x⊔x′
        postable∪ = cff𝑔 (∪-lemma₁ sub⊆𝑓₁ sub⊆𝑓₂) preable∪
        y⊑post∪ = NbhSys.⊑-trans 𝐴 y⊑post₁
                  (Post𝐴.postLemma₁ {postable𝑓 = postable₁}
                  {postable∪})
        y′⊑post∪ = NbhSys.⊑-trans 𝐴 y⊑post₂
                   (Post𝐴.postLemma₂ {postable𝑓′ = postable₂}
                   {postable∪})

↓closedLemma₂ : ∀ {y y′ 𝑔 𝑔′} → NbhSys.Con (𝐴 ⇒ 𝐴) 𝑔 𝑔′ →
                derFrom⊥ 𝑔 y →
                derFrom⊥ 𝑔′ y′ →
                NbhSys.Con 𝐴 y y′
↓closedLemma₂ _ (df⊥-intro₁ y⊑⊥) (df⊥-intro₁ y′⊑⊥)
  = NbhSys.Con-⊔ 𝐴 y⊑⊥ y′⊑⊥
↓closedLemma₂ _ (df⊥-intro₁ y⊑⊥) (df⊥-intro₂ _ _)
  = NbhSys.Con-⊔ 𝐴 y⊑y′ (NbhSys.⊑-refl 𝐴)
  where y⊑y′ = NbhSys.⊑-trans 𝐴 y⊑⊥ (NbhSys.⊑-⊥ 𝐴)
↓closedLemma₂ _ (df⊥-intro₂ _ _) (df⊥-intro₁ y′⊑⊥)
  = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) y′⊑y
  where y′⊑y = NbhSys.⊑-trans 𝐴 y′⊑⊥ (NbhSys.⊑-⊥ 𝐴)
↓closedLemma₂ (con-∪ _ _ cff𝑔) (df⊥-intro₂ df⊥𝑓x xy⊑𝑓)
  (df⊥-intro₂ df⊥𝑓′x′ x′y′⊑𝑓′)
  = ↓closedLemma₂' cff𝑔 conxx′ xy⊑𝑔⊔𝑔′ x′y′⊑𝑔⊔𝑔′
  where con𝑔𝑔′ = (con-∪ _ _ cff𝑔)
        conxx′ = ↓closedLemma₂ con𝑔𝑔′ df⊥𝑓x df⊥𝑓′x′
        xy⊑𝑔⊔𝑔′ = ⊑-⊔-lemma₄ (𝐴 ⇒ 𝐴) xy⊑𝑓 con𝑔𝑔′
        x′y′⊑𝑔⊔𝑔′ = ⊑-⊔-lemma₅ (𝐴 ⇒ 𝐴) x′y′⊑𝑓′ con𝑔𝑔′

↓closedLemma₃' : {x : NbhSys.Nbh 𝐴} →  ∀ {x′ fp fp′} →
                 ∀ confpfp′ → ∀ {𝑓} →
                 𝑓 ⊆ ((x , fp) ∷ ((x′ , fp′) ∷ ∅)) →
                 ∀ {x″ y″} → (x″ , y″) ∈ 𝑓 →
                 [ 𝐴 ] y″ ⊑ ([ 𝐴 ] fp ⊔ fp′ [ confpfp′ ])
↓closedLemma₃' confpfp′ 𝑓⊆ x″y″∈𝑓 with (𝑓⊆ x″y″∈𝑓)
... | here
  = NbhSys.⊑-⊔-fst 𝐴 confpfp′
... | there here
  = NbhSys.⊑-⊔-snd 𝐴 confpfp′

↓closedLemma₃ : ∀ {x fp x′ fp′} → NbhSys.Con 𝐴 fp fp′ →
                ∀ {𝑓} → 𝑓 ⊆ ((x , fp) ∷ ((x′ , fp′) ∷ ∅)) →
                Pre𝐴.Preable 𝑓 → Post𝐴.Postable 𝑓
↓closedLemma₃ confpfp′ f⊆ _
  = Post𝐴.boundedPostable (↓closedLemma₃' confpfp′ f⊆)

↓closedLemma₄' : ∀ {x fp x′ fp′ conxfp conx′fp′ conp conxx′ confpfp′ 𝑓 con𝑓} →
                [ 𝐴 ⇒ 𝐴 ] ([ 𝐴 ⇒ 𝐴 ] 𝐹 ((x , fp) ∷ ∅) conxfp ⊔
                  𝐹 ((x′ , fp′) ∷ ∅) conx′fp′ [ conp ]) ⊑ 𝐹 𝑓 con𝑓 →
                ∀ {x″ y″} → (x″ , y″) ∈ (([ 𝐴 ] x ⊔ x′ [ conxx′ ] ,
                  [ 𝐴 ] fp ⊔ fp′ [ confpfp′ ]) ∷ ∅) →
                ⊑ₑ-proof 𝐴 𝐴 𝑓 con𝑓 x″ y″
↓closedLemma₄' {conp = con-∪ _ _ _} {conxx′} {confpfp′}
  {con𝑓 = cff cff𝑓} (⊑ₑ-intro₂ _ _ p) here
  with (p here) | (p (there here))
... | record { sub = sub₁
             ; sub⊆𝑓 = sub⊆𝑓₁
             ; preablesub = preable₁
             ; postablesub = postable₁
             ; y⊑post = y⊑post₁
             ; pre⊑x = pre⊑x₁
             }
    | record { sub = sub₂
             ; sub⊆𝑓 = sub⊆𝑓₂
             ; preablesub = preable₂
             ; postablesub = postable₂
             ; y⊑post = y⊑post₂
             ; pre⊑x = pre⊑x₂
             }
  = record
      { sub = sub₁ ∪ sub₂
      ; sub⊆𝑓 = ∪⊆𝑓
      ; preablesub = preable∪
      ; postablesub = postable∪
      ; y⊑post = NbhSys.⊑-⊔ 𝐴 fp⊑post∪ fp′⊑post∪ confpfp′
      ; pre⊑x = Pre𝐴.preUnionLemma' preable₁ preable₂ preable∪
                presub₁⊑x⊔x′ presub₂⊑x⊔x′
      }
      where ∪⊆𝑓 = ∪-lemma₁ sub⊆𝑓₁ sub⊆𝑓₂
            presub₁⊑x⊔x′ = ⊑-⊔-lemma₄ 𝐴 pre⊑x₁ conxx′
            presub₂⊑x⊔x′ = ⊑-⊔-lemma₅ 𝐴 pre⊑x₂ conxx′
            preable∪ = Pre𝐴.preUnionLemma preable₁ preable₂
                       presub₁⊑x⊔x′ presub₂⊑x⊔x′
            postable∪ = cff𝑓 ∪⊆𝑓 preable∪
            postsub₁⊑post∪ = Post𝐴.postLemma₁ {postable𝑓 = postable₁}
                             {postable∪}
            postsub₂⊑post∪ = Post𝐴.postLemma₂ {postable𝑓′ = postable₂}
                             {postable∪}
            fp⊑post∪ = NbhSys.⊑-trans 𝐴 y⊑post₁ postsub₁⊑post∪
            fp′⊑post∪ = NbhSys.⊑-trans 𝐴 y⊑post₂ postsub₂⊑post∪

↓closedLemma₄ : ∀ {x fp x′ fp′ conxfp conx′fp′ conp conxx′ confpfp′ 𝑓} →
                [ 𝐴 ⇒ 𝐴 ] ([ 𝐴 ⇒ 𝐴 ] 𝐹 ((x , fp) ∷ ∅) conxfp ⊔
                  𝐹 ((x′ , fp′) ∷ ∅) conx′fp′ [ conp ]) ⊑ 𝑓 →
                [ 𝐴 ⇒ 𝐴 ] (𝐹 (([ 𝐴 ] x ⊔ x′ [ conxx′ ] ,
                  [ 𝐴 ] fp ⊔ fp′ [ confpfp′ ]) ∷ ∅)
                  singletonIsCon) ⊑ 𝑓
↓closedLemma₄ {conxfp = conxfp} {conx′fp′} {con-∪ _ _ cffp}
  (⊑ₑ-intro₂ _ _ p)
  = ⊑ₑ-intro₂ _ _ (↓closedLemma₄' {conxfp = conxfp} {conx′fp′}
                   {con-∪ _ _ cffp} (⊑ₑ-intro₂ _ _ p))

fixLemma' : ∀ {𝑔 fp 𝑔′ fp′ con𝑔𝑔′ confpfp′} →
            derFrom⊥ 𝑔 fp →
            derFrom⊥ 𝑔′ fp′ →
            derFrom⊥ [ 𝐴 ⇒ 𝐴 ] 𝑔 ⊔ 𝑔′ [ con𝑔𝑔′ ]
              [ 𝐴 ] fp ⊔ fp′ [ confpfp′ ]
fixLemma' (df⊥-intro₁ fp⊑⊥) (df⊥-intro₁ fp′⊑⊥)
  = df⊥-intro₁ (NbhSys.⊑-⊔ 𝐴 fp⊑⊥ fp′⊑⊥ _)
fixLemma' (df⊥-intro₁ fp⊑⊥) (df⊥-intro₂ df⊥𝑔′x xfp′⊑𝑔′)
  = df⊥-intro₂ df⊥𝑔⊔𝑔′⊥⊔x ⊥⊔x⊑𝑔⊔𝑔′
  where con⊥x = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-⊥ 𝐴) (NbhSys.⊑-refl 𝐴)
        x⊑⊥⊔x = NbhSys.⊑-⊔-snd 𝐴 con⊥x
        fp⊑fp′ = NbhSys.⊑-trans 𝐴 fp⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        fp⊔fp′⊑fp′ = NbhSys.⊑-⊔ 𝐴 fp⊑fp′ (NbhSys.⊑-refl 𝐴) _
        𝑔′⊑𝑔⊔𝑔′ = NbhSys.⊑-⊔-snd (𝐴 ⇒ 𝐴) _
        ⊥⊔x⊑𝑔⊔𝑔′ = ↓closedLemma₁ x⊑⊥⊔x fp⊔fp′⊑fp′ 𝑔′⊑𝑔⊔𝑔′ xfp′⊑𝑔′
        ⊥⊔x⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-⊥ 𝐴) (NbhSys.⊑-refl 𝐴) con⊥x
        df⊥𝑔⊔𝑔′⊥⊔x = liftDerFrom⊥₂ 𝑔′⊑𝑔⊔𝑔′ ⊥⊔x⊑x df⊥𝑔′x
fixLemma' (df⊥-intro₂ df⊥𝑔x xfp⊑𝑔) (df⊥-intro₁ fp′⊑⊥)
  = df⊥-intro₂ df⊥𝑔⊔𝑔′x⊔⊥ x⊔⊥⊑𝑔⊔𝑔′
  where conx⊥ = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
        𝑔⊑𝑔⊔𝑔′ = NbhSys.⊑-⊔-fst (𝐴 ⇒ 𝐴) _
        fp′⊑fp = NbhSys.⊑-trans 𝐴 fp′⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        fp⊔fp′⊑fp = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) fp′⊑fp _
        x⊑x⊔⊥ = NbhSys.⊑-⊔-fst 𝐴 conx⊥
        x⊔⊥⊑𝑔⊔𝑔′ = ↓closedLemma₁ x⊑x⊔⊥ fp⊔fp′⊑fp 𝑔⊑𝑔⊔𝑔′ xfp⊑𝑔
        x⊔⊥⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴) conx⊥
        df⊥𝑔⊔𝑔′x⊔⊥ = liftDerFrom⊥₂ 𝑔⊑𝑔⊔𝑔′ x⊔⊥⊑x df⊥𝑔x
fixLemma' {con𝑔𝑔′ = con𝑔𝑔′} {confpfp′}
  (df⊥-intro₂ df⊥𝑔x xfp⊑𝑔)
  (df⊥-intro₂ df⊥𝑔′x′ x′fp′⊑𝑔′)
  = df⊥-intro₂ (fixLemma' {confpfp′ = conxx′} df⊥𝑔x df⊥𝑔′x′)
    (↓closedLemma₄ {conxfp = singletonIsCon}
    {singletonIsCon} {conxfpx′fp′} ⊔⊑𝑔⊔𝑔′)
  where conxx′ = ↓closedLemma₂ con𝑔𝑔′ df⊥𝑔x df⊥𝑔′x′
        conxfpx′fp′ = (con-∪ _ _ (cff (↓closedLemma₃ confpfp′)))
        ⊔⊑𝑔⊔𝑔′ = ⊑-⊔-lemma₃ (𝐴 ⇒ 𝐴) conxfpx′fp′ con𝑔𝑔′ xfp⊑𝑔 x′fp′⊑𝑔′
        x⊑x⊔x′ = NbhSys.⊑-⊔-fst 𝐴 conxx′

fixLemma : ∀ {𝑓 preable𝑓 postable𝑓} →
           (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓 → derFrom⊥ 𝑔 fp) →
           derFrom⊥ (pre 𝑓 preable𝑓) (post 𝑓 postable𝑓)
fixLemma {∅} _ = df⊥-intro₁ (NbhSys.⊑-refl 𝐴)
fixLemma {(x , y) ∷ 𝑓} {pre-cons preable𝑓 conxpre𝑓}
  {post-cons postable𝑓 conypost𝑓} p
  with (fixLemma {𝑓} {preable𝑓} {postable𝑓}
       (λ 𝑔fp∈𝑓 → p (there 𝑔fp∈𝑓)))
... | df⊥pp = fixLemma' (p here) df⊥pp
