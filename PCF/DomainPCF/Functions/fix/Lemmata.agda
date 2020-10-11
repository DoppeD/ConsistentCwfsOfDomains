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
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐴

↓closedLemma₁' : ∀ {x y y′ conxy} → [ 𝐴 ] y′ ⊑ y →
                 ∀ {x″ y″} → (x″ , y″) ∈ ((x , y′) ∷ ∅) →
                 ⊑ₑ-proof 𝐴 𝐴 ((x , y) ∷ ∅) conxy x″ y″
↓closedLemma₁' {x} {y} y′⊑y here
  = record { sub = (x , y) ∷ ∅
           ; sub⊆𝑓 = ⊆-refl
           ; preablesub = singletonIsPreable
           ; postablesub = singletonIsPostable
           ; y⊑post = ⊑-⊔-lemma₄ 𝐴 y′⊑y cony⊥
           ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴)
                     (NbhSys.⊑-⊥ 𝐴) conx⊥
           }
  where cony⊥ = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴)
                (NbhSys.⊑-⊥ 𝐴)
        conx⊥ = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴)
                (NbhSys.⊑-⊥ 𝐴)

↓closedLemma₁ : ∀ {𝑓 𝑓′ x y y′ conxy conxy′} →
                [ 𝐴 ] y′ ⊑ y → [ 𝐴 ⇒ 𝐴 ] 𝑓 ⊑ 𝑓′ →
                [ 𝐴 ⇒ 𝐴 ] (𝐹 ((x , y) ∷ ∅) conxy) ⊑ 𝑓 →
                [ 𝐴 ⇒ 𝐴 ] (𝐹 ((x , y′) ∷ ∅) conxy′) ⊑ 𝑓′
↓closedLemma₁ y′⊑y 𝑓⊑𝑓′ xy⊑𝑓
  = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) xy′⊑xy xy⊑𝑓′
  where xy⊑𝑓′ = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) xy⊑𝑓 𝑓⊑𝑓′
        xy′⊑xy = ⊑ₑ-intro₂ _ _ (↓closedLemma₁' y′⊑y)

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
        preable∪ = preUnionLemma preable₁ preable₂
                   pre₁⊑x⊔x′ pre₂⊑x⊔x′
        postable∪ = cff𝑔 (∪-lemma₁ sub⊆𝑓₁ sub⊆𝑓₂) preable∪
        y⊑post∪ = NbhSys.⊑-trans 𝐴 y⊑post₁
                  (postLemma₁ {postable𝑓 = postable₁}
                  {postable∪})
        y′⊑post∪ = NbhSys.⊑-trans 𝐴 y⊑post₂
                   (postLemma₂ {postable𝑓′ = postable₂}
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

liftDerFrom⊥ : ∀ {𝑓 𝑓′ x} → [ 𝐴 ⇒ 𝐴 ] 𝑓 ⊑ 𝑓′ →
               derFrom⊥ 𝑓 x →
               derFrom⊥ 𝑓′ x
liftDerFrom⊥ _ (df⊥-intro₁ x⊑⊥) = df⊥-intro₁ x⊑⊥
liftDerFrom⊥ 𝑓⊑𝑓′ (df⊥-intro₂ df𝑓x′ xx′⊑𝑓)
  = df⊥-intro₂ df𝑓′x′ xx′⊑𝑓′
  where df𝑓′x′ = liftDerFrom⊥ 𝑓⊑𝑓′ df𝑓x′
        xx′⊑𝑓′ = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) xx′⊑𝑓 𝑓⊑𝑓′
