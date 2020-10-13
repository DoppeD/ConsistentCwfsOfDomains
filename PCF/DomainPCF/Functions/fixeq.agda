{-# OPTIONS --safe #-}

open import Base.Core

module PCF.DomainPCF.Functions.fixeq (𝐴 : Ty) where

open import Appmap.Definition
open import Appmap.Equivalence
open import Base.FinFun
open import Base.Variables hiding (𝐴)
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.fix.AxiomProofs
open import PCF.DomainPCF.Functions.fix.Instance
open import PCF.DomainPCF.Functions.fix.Lemmata
open import PCF.DomainPCF.Functions.fix.Relation
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre (𝐴 ⇒ 𝐴) 𝐴
import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun (𝐴 ⇒ 𝐴) 𝐴
  as CFF𝐴

fixeqLemma₁'' : ∀ {sub preable postable consub x y} →
                (x , y) ∈
                  ((pre sub preable , post sub postable) ∷ ∅) →
                ⊑ₑ-proof (𝐴 ⇒ 𝐴) 𝐴 sub consub x y
fixeqLemma₁'' {sub} {preable} {postable} here
  = record
      { sub = sub
      ; sub⊆𝑓 = ⊆-refl
      ; preablesub = preable
      ; postablesub = postable
      ; y⊑post = NbhSys.⊑-refl 𝐴
      ; pre⊑x = NbhSys.⊑-refl (𝐴 ⇒ 𝐴)
      }

fixeqLemma₁' : ∀ {𝑓 con𝑓 sub} →  sub ⊆ 𝑓 →
               ∀ {x y} → (x , y) ∈ sub →
               ⊑ₑ-proof (𝐴 ⇒ 𝐴) 𝐴 𝑓 con𝑓 x y
fixeqLemma₁' sub⊆𝑓 {x} {y} xy∈sub
  = record
      { sub = (x , y) ∷ ∅
      ; sub⊆𝑓 = ⊆-lemma₅ (sub⊆𝑓 xy∈sub)
      ; preablesub = singletonIsPreable
      ; postablesub = singletonIsPostable
      ; y⊑post = ⊑-⊔-lemma₄ 𝐴 y⊑y cony⊥
      ; pre⊑x = NbhSys.⊑-⊔ (𝐴 ⇒ 𝐴) x⊑x ⊥⊑x conx⊥
      }
  where y⊑y = NbhSys.⊑-refl 𝐴
        ⊥⊑y = NbhSys.⊑-⊥ 𝐴
        x⊑x = NbhSys.⊑-refl (𝐴 ⇒ 𝐴)
        ⊥⊑x = NbhSys.⊑-⊥ (𝐴 ⇒ 𝐴)
        cony⊥ = NbhSys.Con-⊔ 𝐴 y⊑y ⊥⊑y
        conx⊥ = NbhSys.Con-⊔ (𝐴 ⇒ 𝐴) x⊑x ⊥⊑x

fixeqLemma₁ : {f : Term Γ (𝐴 ⇒ 𝐴)} →
              {𝑥 : Valuation Γ} → ∀ {y} →
              [ ap fix f ] 𝑥 ↦ y →
              [ ap f (ap fix f) ] 𝑥 ↦ y
fixeqLemma₁ (ap↦-intro₁ y⊑⊥) = ap↦-intro₁ y⊑⊥
fixeqLemma₁ (ap↦-intro₂ _ _ _ _ (⊑ₑ-intro₂ _ _ p))
  with (p here)
fixeqLemma₁ (ap↦-intro₂ _ _ (fix↦-intro₂ p₁) _ _)
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           }
  with (fix↦-↓closed'' {𝑓 = sub} {preable} {postable}
        λ 𝑔fp∈sub → p₁ (sub⊆𝑓 𝑔fp∈sub))
fixeqLemma₁ {f = f} (ap↦-intro₂ _ _ _ _  _)
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊏qx
           }
  | df⊥-intro₁ post⊑⊥
  = ap↦-intro₁ (NbhSys.⊑-trans 𝐴 y⊑post post⊑⊥)
fixeqLemma₁ {f = f} (ap↦-intro₂ {x = 𝑔} {y = y} {𝑓 = 𝑓} con𝑓 conxy fix𝑥↦𝑓 f𝑥↦𝑔 (⊑ₑ-intro₂ _ _ p))
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  | df⊥-intro₂ {x = x′} _ x′post⊑pre
  = ap↦-intro₂ {x = post sub postable} singletonIsCon singletonIsCon f𝑥↦x′post
    (ap↦-intro₂ (CFF𝐴.subsetIsCon con𝑓 sub⊆𝑓) CFF𝐴.singletonIsCon sdf f𝑥↦pre
    (⊑ₑ-intro₂ _ _ fixeqLemma₁'')) psyy⊑x′ps
    where f𝑥↦pre = Appmap.↦-↓closed f pre⊑x f𝑥↦𝑔
          sdf = Appmap.↦-↓closed fix
                (⊑ₑ-intro₂ _ _ (fixeqLemma₁' sub⊆𝑓)) fix𝑥↦𝑓
          x′post⊑𝑔 = NbhSys.⊑-trans (𝐴 ⇒ 𝐴) x′post⊑pre pre⊑x
          f𝑥↦x′post = Appmap.↦-↓closed f x′post⊑𝑔 f𝑥↦𝑔
          psyy⊑x′ps = {!!}
{-
fixeqLemma₂ : {f : Term Γ (𝐴 ⇒ 𝐴)} →
              {𝑥 : Valuation Γ} → ∀ {y} →
              [ ap f (ap fix f) ] 𝑥 ↦ y →
              [ ap fix f ] 𝑥 ↦ y
fixeqLemma₂ (ap↦-intro₁ y⊑⊥) = ap↦-intro₁ y⊑⊥
fixeqLemma₂ (ap↦-intro₂ {y = y} con𝑓 conxy x (ap↦-intro₁ x₃⊑⊥) x₂)
  = ap↦-intro₂ {𝑓 = (𝐹 _ con𝑓 , y) ∷ ∅} CFF𝐴.singletonIsCon CFF𝐴.singletonIsCon (fix↦-intro₂ {!!}) x (NbhSys.⊑-refl ((𝐴 ⇒ 𝐴) ⇒ 𝐴))
  -- Take subset sub ⊆ 𝑓 such that pre sub ⊑ x₁ ⊑ ⊥  and y ⊑ post sub.
  -- We can show derFrom⊥ sub ⊥, and we have ((⊥ , y) ⊑ sub, so derFrom⊥ sub y.
  -- Hence derFrom⊥ 𝑓 y.
fixeqLemma₂ (ap↦-intro₂ con𝑓 conxy x (ap↦-intro₂ con𝑓₁ conxy₁ x₁ x₃ x₄) x₂)
  = {!!}

fixeq : {f : Term Γ (𝐴 ⇒ 𝐴)} →
        ap {Γ = Γ} fix f ≈ ap f (ap fix f)
fixeq = ≈-intro (≼-intro fixeqLemma₁)
        (≼-intro fixeqLemma₂)
-}
