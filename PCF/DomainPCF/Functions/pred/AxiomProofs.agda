{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.pred.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.pred.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Nat

pred↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →
             𝑥 pred↦ z → 𝑦 pred↦ z
pred↦-mono _ pred↦-intro₁
  = pred↦-intro₁
pred↦-mono _ (pred↦-intro₂ p)
  = pred↦-intro₂ p

pred↦-bottom : {𝑥 : Valuation Γ} → 𝑥 pred↦ ⊥ₑ
pred↦-bottom = pred↦-intro₁

pred↦-↓closed''' : ∀ {x y x′ y′} → predprop x y →
                   predprop x′ y′ → ∀ conxx′ conyy′ →
                   predprop (x ⊔ₙ x′ [ conxx′ ]) (y ⊔ₙ y′ [ conyy′ ])
pred↦-↓closed''' (pprop₁ x⊑0 y⊑⊥) (pprop₁ x′⊑0 y′⊑⊥) conxx′ conyy′
  = pprop₁ x⊔x′⊑0 y⊔y′⊑⊥
  where x⊔x′⊑0 = NbhSys.⊑-⊔ Nat x⊑0 x′⊑0 conxx′
        y⊔y′⊑⊥ = NbhSys.⊑-⊔ Nat y⊑⊥ y′⊑⊥ conyy′
pred↦-↓closed''' (pprop₁ ⊑ₙ-intro₁ ⊑ₙ-intro₁)
  (pprop₂ (⊑ₙ-intro₃ y′⊑y)) conₙ-bot₁ conyy′
  = pprop₂ (⊑ₙ-intro₃ (⊥⊔y′⊑y))
  where ⊥⊔y′⊑y = NbhSys.⊑-⊔ Nat (NbhSys.⊑-⊥ Nat) y′⊑y conyy′
pred↦-↓closed''' (pprop₂ (⊑ₙ-intro₃ y⊑x))
  (pprop₁ _ ⊑ₙ-intro₁) conₙ-bot₂ conyy′
  = pprop₂ (⊑ₙ-intro₃ y⊔⊥⊑x)
  where y⊔⊥⊑x = NbhSys.⊑-⊔ Nat y⊑x (NbhSys.⊑-⊥ Nat) conyy′
pred↦-↓closed''' (pprop₂ (⊑ₙ-intro₃ y⊑x))
  (pprop₂ (⊑ₙ-intro₃ y′⊑x′)) (conₙ-sₙ conxx′) conyy′
  = pprop₂ (⊑ₙ-intro₃ y⊔y′⊑x⊔x′)
  where y⊔y′⊑x⊔x′ = ⊑-⊔-lemma₃ Nat conyy′ conxx′ y⊑x y′⊑x′

pred↦-↓closed'' : ∀ {sub preable postable} →
                  (∀ {x y} → (x , y) ∈ sub → predprop x y) →
                  predprop (pre sub preable) (post sub postable)
pred↦-↓closed'' {∅} _ = pprop₁ ⊑ₙ-intro₁ ⊑ₙ-intro₁
pred↦-↓closed'' {_ ∷ _} {pre-cons _ conxpresub}
  {post-cons _ conypostsub} p
  = pred↦-↓closed''' ppxy ppprepost conxpresub conypostsub
  where ppxy = p here
        ppprepost = pred↦-↓closed'' (λ xy∈sub → p (there xy∈sub))

pred↦-↓closed' : ∀ {𝑓 𝑓′ con𝑓′} →
                 (∀ {x y} → (x , y) ∈ 𝑓 → ⊑ₑ-proof 𝑓′ con𝑓′ x y) →
                 (∀ {x y} → (x , y) ∈ 𝑓′ → predprop x y) →
                 ∀ {x y} → (x , y) ∈ 𝑓 → predprop x y
pred↦-↓closed' p₁ p₂ xy∈𝑓 with (p₁ xy∈𝑓)
... | record { sub = sub
             ; sub⊆𝑓 = sub⊆𝑓
             ; preablesub = preable
             ; postablesub = postable
             }
  with (pred↦-↓closed'' {sub} {preable} {postable}
       (λ xy∈sub → p₂ (sub⊆𝑓 xy∈sub)))
pred↦-↓closed' p₁ p₂ {⊥ₙ} xy∈𝑓
  | record { y⊑post = y⊑post ; pre⊑x = pre⊑x }
  | pprop₁ pre⊑0 post⊑⊥
  = pprop₁ ⊑ₙ-intro₁ y⊑⊥
  where y⊑⊥ = NbhSys.⊑-trans Nat y⊑post post⊑⊥
pred↦-↓closed' p₁ p₂ {0ₙ} xy∈𝑓
  | record { y⊑post = y⊑post ; pre⊑x = pre⊑x }
  | pprop₁ pre⊑0 post⊑⊥
  = pprop₁ ⊑ₙ-intro₂ y⊑⊥
  where y⊑⊥ = NbhSys.⊑-trans Nat y⊑post post⊑⊥
pred↦-↓closed' p₁ p₂ {sₙ x} xy∈𝑓
  | record { y⊑post = y⊑post ; pre⊑x = pre⊑x }
  | pprop₁ pre⊑0 post⊑⊥
  = pprop₂ (⊑ₙ-intro₃ y⊑x)
  where post⊑x = NbhSys.⊑-trans Nat post⊑⊥ ⊑ₙ-intro₁
        y⊑x = NbhSys.⊑-trans Nat y⊑post post⊑x
pred↦-↓closed' p₁ p₂ xy∈𝑓
  | record { y⊑post = y⊑post ; pre⊑x = pre⊑x }
  | pprop₂ pre⊑spost
  = pprop₂ (NbhSys.⊑-trans Nat (⊑ₙ-intro₃ y⊑post) spost⊑x)
  where spost⊑x = NbhSys.⊑-trans Nat pre⊑spost pre⊑x

pred↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑ₑ z →
                𝑥 pred↦ z → 𝑥 pred↦ y
pred↦-↓closed ⊑ₑ-intro₁ _
  = pred↦-intro₁
pred↦-↓closed (⊑ₑ-intro₂ a b p₁) (pred↦-intro₂ p₂)
  = pred↦-intro₂ (pred↦-↓closed' p₁ p₂)

pred↦-↑directed' : ∀ {𝑓 𝑓′} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → predprop x y) →
                   (∀ {x y} → (x , y) ∈ 𝑓′ → predprop x y) →
                   ∀ {x y} → (x , y) ∈ (𝑓 ∪ 𝑓′) →
                   predprop x y
pred↦-↑directed' {𝑓} p₁ p₂ xy∈∪ with (∪-lemma₂ {𝑓 = 𝑓} xy∈∪)
... | inl xy∈𝑓 = p₁ xy∈𝑓
... | inr xy∈𝑓′ = p₂ xy∈𝑓′

pred↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} →
                  𝑥 pred↦ y → 𝑥 pred↦ z →
                  ∀ conyz → 𝑥 pred↦ (y ⊔ₑ z [ conyz ])
pred↦-↑directed pred↦-intro₁ pred↦-intro₁ _
  = pred↦-intro₁
pred↦-↑directed pred↦-intro₁ (pred↦-intro₂ p) conₑ-⊥₂
  = pred↦-intro₂ p
pred↦-↑directed (pred↦-intro₂ p) pred↦-intro₁ conₑ-⊥₁
  = pred↦-intro₂ p
pred↦-↑directed (pred↦-intro₂ p₁) (pred↦-intro₂ p₂) (con-∪ _ _ _)
  = pred↦-intro₂ (pred↦-↑directed' p₁ p₂)

pred↦-con'' : ∀ {x y x′ y′} →
              predprop x y → predprop x′ y′ →
              NbhSys.Con Nat x x′ →
              NbhSys.Con Nat y y′
pred↦-con'' (pprop₁ _ ⊑ₙ-intro₁) _ _
  = conₙ-bot₁
pred↦-con'' (pprop₂ _) (pprop₁ _ ⊑ₙ-intro₁) _
  = conₙ-bot₂
pred↦-con'' (pprop₂ (⊑ₙ-intro₃ y⊑x))
  (pprop₂ (⊑ₙ-intro₃ y′⊑x′)) (conₙ-sₙ conxx′)
  = NbhSys.Con-⊔ Nat y⊑x⊔x′ y′⊑x⊔x′
  where y⊑x⊔x′ = ⊑-⊔-lemma₄ Nat y⊑x conxx′
        y′⊑x⊔x′ = ⊑-⊔-lemma₅ Nat y′⊑x′ conxx′

pred↦-con' : ∀ {𝑔} →
             (∀ {x y} → (x , y) ∈ 𝑔 → predprop x y) →
             Preable 𝑔 → Postable 𝑔
pred↦-con' {∅} _ _ = post-nil
pred↦-con' {_ ∷ _} p (pre-cons preable𝑔 conxpre𝑔)
  with (p here) | pred↦-↓closed'' {preable = preable𝑔} {rec}
                  λ xy∈𝑔 → p (there xy∈𝑔)
  where rec = pred↦-con' (λ xy∈𝑔 → p (there xy∈𝑔)) preable𝑔
... | zp₁ | zp₂ = post-cons rec (pred↦-con'' zp₁ zp₂ conxpre𝑔)
  where rec = pred↦-con' (λ xy∈𝑔 → p (there xy∈𝑔)) preable𝑔

pred↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
            𝑥 pred↦ y → 𝑥′ pred↦ y′ →
            ValCon _ 𝑥 𝑥′ → ArrCon y y′
pred↦-con pred↦-intro₁ pred↦-intro₁ _ = conₑ-⊥₁
pred↦-con pred↦-intro₁ (pred↦-intro₂ _) _ = conₑ-⊥₂
pred↦-con (pred↦-intro₂ _) pred↦-intro₁ _ = conₑ-⊥₁
pred↦-con (pred↦-intro₂ p₁) (pred↦-intro₂ p₂) _
  = con-∪ _ _ (cff λ 𝑔⊆∪ preable𝑔 →
    pred↦-con' (λ xy∈𝑔 → pp𝑔 (𝑔⊆∪ xy∈𝑔)) preable𝑔)
  where pp𝑔 = pred↦-↑directed' p₁ p₂
