{-# OPTIONS --safe #-}

open import Base.Core

module PCF.DomainPCF.Functions.fixeq (𝐴 : Ty) where

open import Appmap.Definition
open import Appmap.Equivalence
open import Base.FinFun
open import Base.Variables hiding (𝐴)
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.fix.Instance
open import PCF.DomainPCF.Functions.fix.Lemmata
open import PCF.DomainPCF.Functions.fix.Relation
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre (𝐴 ⇒ 𝐴) 𝐴
import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐴
  as CFF𝐴

fixeqLemma₁'' : ∀ {𝑔 y} →
                derFrom⊥ 𝐴 𝑔 y →
                ∀ {𝑔′ y′} → (𝑔′ , y′) ∈ ((𝑔 , y) ∷ ∅) →
                derFrom⊥ 𝐴 𝑔′ y′
fixeqLemma₁'' df⊥𝑔y here = df⊥𝑔y

fixeqLemma₁' : {f : Term Γ (𝐴 ⇒ 𝐴)} →
               {𝑥 : Valuation Γ} → ∀ {y 𝑔} →
               [ f ] 𝑥 ↦ 𝑔 →
               derFrom⊥ 𝐴 𝑔 y →
               [ ap fix f ] 𝑥 ↦ y
fixeqLemma₁' {y = y} {𝑔} f𝑥↦𝑔 df⊥𝑔y
  = ap↦-intro₂ singletonIsCon singletonIsCon
    (fix↦-intro₂ (fixeqLemma₁'' df⊥𝑔y)) f𝑥↦𝑔
    (NbhSys.⊑-refl ((𝐴 ⇒ 𝐴) ⇒ 𝐴))

fixeqLemma : {𝑥 : Valuation Γ} →
             ∀ {𝑓 con𝑓 𝑔 y con𝑔y} →
             [ fix ] 𝑥 ↦ 𝐹 𝑓 con𝑓 →
             [ (𝐴 ⇒ 𝐴) ⇒ 𝐴 ] 𝐹 ((𝑔 , y) ∷ ∅) con𝑔y ⊑ 𝐹 𝑓 con𝑓 →
             derFrom⊥ 𝐴 𝑔 y
fixeqLemma _ (⊑ₑ-intro₂ _ _ p)
  with (p here)
fixeqLemma (fix↦-intro₂ p) _
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = liftDerFrom⊥₂ pre⊑x y⊑post df⊥prepost
  where df⊥prepost = fixLemma {𝑓 = sub} {preable} {postable}
                     (λ xy∈sub → p (sub⊆𝑓 xy∈sub))
  
fixeqLemma₁ : {f : Term Γ (𝐴 ⇒ 𝐴)} →
              {𝑥 : Valuation Γ} → ∀ {y} →
              [ ap fix f ] 𝑥 ↦ y →
              [ ap f (ap fix f) ] 𝑥 ↦ y
fixeqLemma₁ (ap↦-intro₁ y⊑⊥) = ap↦-intro₁ y⊑⊥
fixeqLemma₁ (ap↦-intro₂ _ _ fix𝑥↦𝑓 _ 𝑔y⊑𝑓)
  with (fixeqLemma fix𝑥↦𝑓 𝑔y⊑𝑓)
fixeqLemma₁ (ap↦-intro₂ _ _ _ _ _)
  | df⊥-intro₁ y⊑⊥
  = ap↦-intro₁ y⊑⊥
fixeqLemma₁ (ap↦-intro₂ {x = ⊥ₑ} _ _ _ _ _)
  | df⊥-intro₂ _ ()
fixeqLemma₁ (ap↦-intro₂ {x = 𝐹 𝑔 con𝑔} _ _ _ f𝑥↦𝑔 _)
  | df⊥-intro₂ df⊥𝑔y′ y′y⊑𝑔
  = ap↦-intro₂ con𝑔 CFF𝐴.singletonIsCon f𝑥↦𝑔 apfixf𝑥↦y′ y′y⊑𝑔
  where apfixf𝑥↦y′ = fixeqLemma₁' f𝑥↦𝑔 df⊥𝑔y′

fixeqLemma₂' : ∀ {𝑔 fp} →
               derFrom⊥ 𝐴 𝑔 fp →
               ∀ {𝑔′ fp′} → (𝑔′ , fp′) ∈ ((𝑔 , fp) ∷ ∅) →
               derFrom⊥ 𝐴 𝑔′ fp′
fixeqLemma₂' df⊥𝑔fp here = df⊥𝑔fp

⊑-proofIrr : ∀ {𝑓 con𝑓 con𝑓′ 𝑔} →
             [ 𝐴 ⇒ 𝐴 ] 𝐹 𝑓 con𝑓 ⊑ 𝑔 →
             [ 𝐴 ⇒ 𝐴 ] 𝐹 𝑓 con𝑓′ ⊑ 𝑔
⊑-proofIrr (⊑ₑ-intro₂ _ con𝑓′ p) = ⊑ₑ-intro₂ _ con𝑓′ p

fixeqLemma₂ : {f : Term Γ (𝐴 ⇒ 𝐴)} →
              {𝑥 : Valuation Γ} → ∀ {y} →
              [ ap f (ap fix f) ] 𝑥 ↦ y →
              [ ap fix f ] 𝑥 ↦ y
fixeqLemma₂ (ap↦-intro₁ y⊑⊥) = ap↦-intro₁ y⊑⊥
fixeqLemma₂ (ap↦-intro₂ con𝑔 conxy f𝑥↦𝑔 (ap↦-intro₁ x⊑⊥) xy⊑𝑔)
  = ap↦-intro₂ singletonIsCon singletonIsCon
    (fix↦-intro₂ (fixeqLemma₁'' df⊥𝑔y)) f𝑥↦𝑔
    (NbhSys.⊑-refl ((𝐴 ⇒ 𝐴) ⇒ 𝐴))
  where 𝑔⊑𝑔 = NbhSys.⊑-refl (𝐴 ⇒ 𝐴)
        xy⊑𝑔₂ = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) (⊑-proofIrr xy⊑𝑔) 𝑔⊑𝑔
        df⊥𝑔y = df⊥-intro₂ (df⊥-intro₁ x⊑⊥) xy⊑𝑔₂
        
fixeqLemma₂ {f = f} (ap↦-intro₂ _ _ f𝑥↦𝑔
  (ap↦-intro₂ _ _ fix𝑥↦𝑓 f𝑥↦𝑔′ 𝑔′x⊑𝑓) xy⊑𝑔)
  = ap↦-intro₂ singletonIsCon singletonIsCon fix𝑥↦𝑔⊔𝑔′ f𝑥↦𝑔⊔𝑔′ 
    𝑔⊔𝑔′⊑𝑔⊔𝑔′
  where con𝑔𝑔′ = Appmap.↦-con f f𝑥↦𝑔 f𝑥↦𝑔′ valConRefl
        f𝑥↦𝑔⊔𝑔′ = Appmap.↦-↑directed f f𝑥↦𝑔 f𝑥↦𝑔′ con𝑔𝑔′
        𝑔⊔𝑔′⊑𝑔⊔𝑔′ = NbhSys.⊑-refl ((𝐴 ⇒ 𝐴) ⇒ 𝐴)
        𝑔⊑𝑔⊔𝑔′ = NbhSys.⊑-⊔-fst (𝐴 ⇒ 𝐴) con𝑔𝑔′
        𝑔′⊑𝑔⊔𝑔′ = NbhSys.⊑-⊔-snd (𝐴 ⇒ 𝐴) con𝑔𝑔′
        xy⊑𝑔⊔𝑔′ = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) (⊑-proofIrr xy⊑𝑔) 𝑔⊑𝑔⊔𝑔′
        df⊥𝑔′x = fixeqLemma fix𝑥↦𝑓 𝑔′x⊑𝑓
        df⊥𝑔⊔𝑔y = df⊥-intro₂ (liftDerFrom⊥ 𝑔′⊑𝑔⊔𝑔′ df⊥𝑔′x) xy⊑𝑔⊔𝑔′
        fix𝑥↦𝑔⊔𝑔′ = fix↦-intro₂ (fixeqLemma₂' df⊥𝑔⊔𝑔y)

fixeq : (f : Term Γ (𝐴 ⇒ 𝐴)) →
        ap {Γ = Γ} fix f ≈ ap f (ap fix f)
fixeq f = ≈-intro (≼-intro fixeqLemma₁)
          (≼-intro fixeqLemma₂)
