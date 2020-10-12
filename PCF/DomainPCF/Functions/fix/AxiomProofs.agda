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
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre (𝐴 ⇒ 𝐴) 𝐴
import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun (𝐴 ⇒ 𝐴) 𝐴 as CFF𝐴

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

fix↦-↓closed''' : ∀ {𝑔 fp 𝑔′ fp′ con𝑔𝑔′ confpfp′} →
                  derFrom⊥ 𝑔 fp →
                  derFrom⊥ 𝑔′ fp′ →
                  derFrom⊥ [ 𝐴 ⇒ 𝐴 ] 𝑔 ⊔ 𝑔′ [ con𝑔𝑔′ ]
                    [ 𝐴 ] fp ⊔ fp′ [ confpfp′ ]
fix↦-↓closed''' (df⊥-intro₁ fp⊑⊥) (df⊥-intro₁ fp′⊑⊥)
  = df⊥-intro₁ (NbhSys.⊑-⊔ 𝐴 fp⊑⊥ fp′⊑⊥ _)
fix↦-↓closed''' (df⊥-intro₁ fp⊑⊥) (df⊥-intro₂ df⊥𝑔′x xfp′⊑𝑔′)
  = df⊥-intro₂ df⊥𝑔⊔𝑔′⊥⊔x ⊥⊔x⊑𝑔⊔𝑔′
  where con⊥x = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-⊥ 𝐴) (NbhSys.⊑-refl 𝐴)
        df⊥𝑔⊔𝑔′⊥⊔x = ↓closedLemma₄ con⊥x df⊥𝑔′x
        x⊑⊥⊔x = NbhSys.⊑-⊔-snd 𝐴 con⊥x
        fp⊑fp′ = NbhSys.⊑-trans 𝐴 fp⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        fp⊔fp′⊑fp′ = NbhSys.⊑-⊔ 𝐴 fp⊑fp′ (NbhSys.⊑-refl 𝐴) _
        𝑔′⊑𝑔⊔𝑔′ = NbhSys.⊑-⊔-snd (𝐴 ⇒ 𝐴) _
        ⊥⊔x⊑𝑔⊔𝑔′ = ↓closedLemma₁ x⊑⊥⊔x fp⊔fp′⊑fp′ 𝑔′⊑𝑔⊔𝑔′ xfp′⊑𝑔′
fix↦-↓closed''' (df⊥-intro₂ df⊥𝑔x xfp⊑𝑔) (df⊥-intro₁ fp′⊑⊥)
  = df⊥-intro₂ (↓closedLemma₃ conx⊥ df⊥𝑔x) x⊔⊥⊑𝑔⊔𝑔′
  where conx⊥ = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
        𝑔⊑𝑔⊔𝑔′ = NbhSys.⊑-⊔-fst (𝐴 ⇒ 𝐴) _
        fp′⊑fp = NbhSys.⊑-trans 𝐴 fp′⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        fp⊔fp′⊑fp = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) fp′⊑fp _
        x⊑x⊔⊥ = NbhSys.⊑-⊔-fst 𝐴 conx⊥
        x⊔⊥⊑𝑔⊔𝑔′ = ↓closedLemma₁ x⊑x⊔⊥ fp⊔fp′⊑fp 𝑔⊑𝑔⊔𝑔′ xfp⊑𝑔
fix↦-↓closed''' {con𝑔𝑔′ = con𝑔𝑔′} {confpfp′}
  (df⊥-intro₂ {x = x} df⊥𝑔x xfp⊑𝑔)
  (df⊥-intro₂ {x = x′} df⊥𝑔′x′ x′fp′⊑𝑔′)
  = df⊥-intro₂ {x = [ 𝐴 ] x ⊔ x′ [ conxx′ ]} (fix↦-↓closed''' df⊥𝑔x df⊥𝑔′x′)
    (↓closedLemma₆ {conxfp = singletonIsCon} {singletonIsCon} {conxfpx′fp′} ⊔⊑𝑔⊔𝑔′)
  where conxx′ = ↓closedLemma₂ con𝑔𝑔′ df⊥𝑔x df⊥𝑔′x′
        conxfpx′fp′ = (con-∪ _ _ (cff (↓closedLemma₅ confpfp′)))
        ⊔⊑𝑔⊔𝑔′ = ⊑-⊔-lemma₃ (𝐴 ⇒ 𝐴) conxfpx′fp′ con𝑔𝑔′ xfp⊑𝑔 x′fp′⊑𝑔′
  
fix↦-↓closed'' : ∀ {𝑓 preable𝑓 postable𝑓} →
                 (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓 → derFrom⊥ 𝑔 fp) →
                 derFrom⊥ (pre 𝑓 preable𝑓) (post 𝑓 postable𝑓)
fix↦-↓closed'' {∅} _ = df⊥-intro₁ (NbhSys.⊑-refl 𝐴)
fix↦-↓closed'' {(x , y) ∷ 𝑓} {pre-cons preable𝑓 conxpre𝑓}
  {post-cons postable𝑓 conypost𝑓} p
  with (fix↦-↓closed'' {𝑓} {preable𝑓} {postable𝑓}
       (λ 𝑔fp∈𝑓 → p (there 𝑔fp∈𝑓)))
... | df⊥pp = fix↦-↓closed''' (p here) df⊥pp

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
  with (fix↦-↓closed'' {preable𝑓 = preable} {postable}
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

fix↦-con'' : ∀ {sub} →
             (∀ {𝑔 fp} → (𝑔 , fp) ∈ sub →
             derFrom⊥ 𝑔 fp) →
             Preable sub → Postable sub
fix↦-con'' {∅} _ _ = post-nil
fix↦-con'' {(𝑔 , fp) ∷ sub} df⊥𝑔fp
  (pre-cons preablesub con𝑔sub)
  = post-cons rec confppostsub
  where rec = fix↦-con'' {sub} (λ 𝑔fp∈sub →
              (df⊥𝑔fp (there 𝑔fp∈sub))) preablesub
        df⊥prepost = fix↦-↓closed''
                     (λ 𝑔fp∈sub → df⊥𝑔fp (there 𝑔fp∈sub))
        confppostsub = ↓closedLemma₂ con𝑔sub (df⊥𝑔fp here)
                        df⊥prepost

fix↦-con' : ∀ {𝑓 𝑓′} →
            (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓 →
            derFrom⊥ 𝑔 fp) →
            (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓′ →
            derFrom⊥ 𝑔 fp) →
            ∀ {𝑔 fp} → (𝑔 , fp) ∈ (𝑓 ∪ 𝑓′) →
            derFrom⊥ 𝑔 fp
fix↦-con' {𝑓} df⊥𝑔fp df⊥𝑔′fp′ 𝑔fp∈∪
  with (∪-lemma₂ {𝑓 = 𝑓} 𝑔fp∈∪)
... | inl 𝑔fp∈𝑓 = df⊥𝑔fp 𝑔fp∈𝑓
... | inr 𝑔fp∈𝑓′ = df⊥𝑔′fp′ 𝑔fp∈𝑓′

fix↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
           𝑥 fix↦ y → 𝑥′ fix↦ y′ → ValCon _ 𝑥 𝑥′ →
           NbhSys.Con ((𝐴 ⇒ 𝐴) ⇒ 𝐴) y y′
fix↦-con fix↦-intro₁ fix↦-intro₁ _ = conₑ-⊥₁
fix↦-con fix↦-intro₁ (fix↦-intro₂ _) _ = conₑ-⊥₂
fix↦-con (fix↦-intro₂ _) fix↦-intro₁ _ = conₑ-⊥₁
fix↦-con (fix↦-intro₂ df⊥𝑔fp) (fix↦-intro₂ df⊥𝑔′fp′) _
  = con-∪ _ _ (CFF𝐴.cff λ sub⊆∪ preable →
    fix↦-con'' (λ 𝑔fp∈sub → shrinkdf (sub⊆∪ 𝑔fp∈sub)) preable)
  where shrinkdf = fix↦-con' df⊥𝑔fp df⊥𝑔′fp′
