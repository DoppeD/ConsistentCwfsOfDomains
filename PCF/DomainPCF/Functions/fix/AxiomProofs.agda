{-# OPTIONS --safe #-}

open import Base.Core

module PCF.DomainPCF.Functions.fix.AxiomProofs
  {𝐴 : Ty} where

open import Base.Core
open import Base.FinFun
open import Base.Variables hiding (𝐴)
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.fix.Lemmata
open import PCF.DomainPCF.Functions.fix.Relation 𝐴
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre (𝐴 ⇒ 𝐴) 𝐴
import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐴
  as CFF𝐴

fix↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →
            𝑥 fix↦ z → 𝑦 fix↦ z
fix↦-mono x fix↦-intro₁ = fix↦-intro₁
fix↦-mono x (fix↦-intro₂ p) = fix↦-intro₂ p

fix↦-bottom : {𝑥 : Valuation Γ} → 𝑥 fix↦ ⊥ₑ
fix↦-bottom = fix↦-intro₁

fix↦-↑directed' : ∀ {𝑓 𝑓′} →
                  (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓 → derFrom⊥ 𝑔 fp) →
                  (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓′ → derFrom⊥ 𝑔 fp) →
                  ∀ {𝑔 fp} → (𝑔 , fp) ∈ (𝑓 ∪ 𝑓′) → derFrom⊥ 𝑔 fp
fix↦-↑directed' {𝑓} p₁ p₂ 𝑔fp∈∪ with (∪-lemma₂ {𝑓 = 𝑓} 𝑔fp∈∪)
... | inl 𝑔fp∈𝑓 = p₁ 𝑔fp∈𝑓
... | inr 𝑔fp∈𝑓′ = p₂ 𝑔fp∈𝑓′

fix↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} →
                 𝑥 fix↦ y → 𝑥 fix↦ z → ∀ conyz →
                 𝑥 fix↦ ([ (𝐴 ⇒ 𝐴) ⇒ 𝐴 ] y ⊔ z [ conyz ])
fix↦-↑directed fix↦-intro₁ fix↦-intro₁ _ = fix↦-intro₁
fix↦-↑directed fix↦-intro₁ (fix↦-intro₂ p) _ = fix↦-intro₂ p
fix↦-↑directed (fix↦-intro₂ p) fix↦-intro₁ _ = fix↦-intro₂ p
fix↦-↑directed (fix↦-intro₂ p₁) (fix↦-intro₂ p₂) (con-∪ _ _ p₃)
  = fix↦-intro₂ (fix↦-↑directed' p₁ p₂)

fix↦-↓closed' : ∀ {𝑓 𝑓′ con𝑓′} →
                (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓 →
                ⊑ₑ-proof (𝐴 ⇒ 𝐴) 𝐴 𝑓′ con𝑓′ 𝑔 fp) →
                (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓′ → derFrom⊥ 𝑔 fp) →
                ∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓 → derFrom⊥ 𝑔 fp
fix↦-↓closed' p₁ p₂ 𝑔fp∈𝑓 with (p₁ 𝑔fp∈𝑓)
fix↦-↓closed' p₁ p₂ 𝑔fp∈𝑓
  | record { sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           }
  with (fixLemma {preable𝑓 = preable} {postable}
       λ 𝑔fp∈sub → p₂ (sub⊆𝑓 𝑔fp∈sub))
fix↦-↓closed' p₁ p₂ 𝑔fp∈𝑓
  | record { y⊑post = y⊑post
           ; pre⊑x = pre⊏qx
           }
  | df⊥-intro₁ post⊑⊥ = df⊥-intro₁ fp⊑⊥
  where fp⊑⊥ = NbhSys.⊑-trans 𝐴 y⊑post post⊑⊥
fix↦-↓closed' p₁ p₂ {fp = fp} 𝑔fp∈𝑓
  | record { y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  | df⊥-intro₂ df⊥prex xpost⊑pre
  = df⊥-intro₂ df⊥𝑔x xfp⊑𝑔
  where df⊥𝑔x = liftDerFrom⊥ pre⊑x df⊥prex
        xfp⊑𝑔 = ↓closedLemma₁ (NbhSys.⊑-refl 𝐴) y⊑post
                pre⊑x xpost⊑pre

fix↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} →
               [ (𝐴 ⇒ 𝐴) ⇒ 𝐴 ] y ⊑ z →
               𝑥 fix↦ z → 𝑥 fix↦ y
fix↦-↓closed ⊑ₑ-intro₁ _ = fix↦-intro₁
fix↦-↓closed (⊑ₑ-intro₂ _ _ p₁) (fix↦-intro₂ p₂)
  = fix↦-intro₂ (fix↦-↓closed' p₁ p₂)

fix↦-con' : ∀ {sub} →
            (∀ {𝑔 fp} → (𝑔 , fp) ∈ sub →
            derFrom⊥ 𝑔 fp) →
            Preable sub → Postable sub
fix↦-con' {∅} _ _ = post-nil
fix↦-con' {(𝑔 , fp) ∷ sub} df⊥𝑔fp
  (pre-cons preablesub con𝑔sub)
  = post-cons rec confppostsub
  where rec = fix↦-con' {sub} (λ 𝑔fp∈sub →
              (df⊥𝑔fp (there 𝑔fp∈sub))) preablesub
        df⊥prepost = fixLemma
                     (λ 𝑔fp∈sub → df⊥𝑔fp (there 𝑔fp∈sub))
        confppostsub = ↓closedLemma₂ con𝑔sub (df⊥𝑔fp here)
                        df⊥prepost

fix↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
           𝑥 fix↦ y → 𝑥′ fix↦ y′ → ValCon _ 𝑥 𝑥′ →
           NbhSys.Con ((𝐴 ⇒ 𝐴) ⇒ 𝐴) y y′
fix↦-con fix↦-intro₁ fix↦-intro₁ _ = conₑ-⊥₁
fix↦-con fix↦-intro₁ (fix↦-intro₂ _) _ = conₑ-⊥₂
fix↦-con (fix↦-intro₂ _) fix↦-intro₁ _ = conₑ-⊥₁
fix↦-con (fix↦-intro₂ df⊥𝑔fp) (fix↦-intro₂ df⊥𝑔′fp′) _
  = con-∪ _ _ (cff λ sub⊆∪ preable →
    fix↦-con' (λ 𝑔fp∈sub → shrinkdf (sub⊆∪ 𝑔fp∈sub)) preable)
  where shrinkdf = fix↦-↑directed' df⊥𝑔fp df⊥𝑔′fp′
