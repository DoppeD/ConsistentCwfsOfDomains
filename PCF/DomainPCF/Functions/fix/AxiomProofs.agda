open import Base.Core

module PCF.DomainPCF.Functions.fix.AxiomProofs
  {𝐴 : Ty} where

open import Base.Core
open import Base.FinFun
open import Base.Variables hiding (𝐴)
open import NbhSys.Definition
open import PCF.DomainPCF.Functions.fix.Lemmata
open import PCF.DomainPCF.Functions.fix.Relation 𝐴
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post (𝐴 ⇒ 𝐴) 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre (𝐴 ⇒ 𝐴) 𝐴

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
fix↦-↓closed''' (df⊥-intro₁ ad) (df⊥-intro₂ {x = x} b x₁) = df⊥-intro₂ {x = x} {!!} {!!}
fix↦-↓closed''' (df⊥-intro₂ {x = x} a ad) (df⊥-intro₁ x₁) = df⊥-intro₂ {x = x} {!!} {!!}
fix↦-↓closed''' {con𝑔𝑔′ = con𝑔𝑔′} (df⊥-intro₂ {x = y} a x) (df⊥-intro₂ {x = z} b x₁)
  = df⊥-intro₂ {x = [ 𝐴 ] y ⊔ z [ ↓closedLemma₂ con𝑔𝑔′ a b ]} (fix↦-↓closed''' a b) {!!}

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
        xfp⊑𝑔 = ↓closedLemma₁ y⊑post pre⊑x xpost⊑pre

fix↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} →
               [ (𝐴 ⇒ 𝐴) ⇒ 𝐴 ] y ⊑ z →
               𝑥 fix↦ z → 𝑥 fix↦ y
fix↦-↓closed ⊑ₑ-intro₁ _ = fix↦-intro₁
fix↦-↓closed (⊑ₑ-intro₂ _ _ p₁) (fix↦-intro₂ p₂)
  = fix↦-intro₂ (fix↦-↓closed' p₁ p₂)
