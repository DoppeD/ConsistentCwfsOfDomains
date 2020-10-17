{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.iszero.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.iszero.Lemmata
open import PCF.DomainPCF.Functions.iszero.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.NbhSys.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Bool

iszero↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →
               𝑥 iszero↦ z → 𝑦 iszero↦ z
iszero↦-mono x iszero↦-intro₁ = iszero↦-intro₁
iszero↦-mono x (iszero↦-intro₂ p) = iszero↦-intro₂ p

iszero↦-bottom : {𝑥 : Valuation Γ} → 𝑥 iszero↦ ⊥ₑ
iszero↦-bottom = iszero↦-intro₁

iszero↦-↓closed' : ∀ {𝑓 𝑓′ con𝑓′} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → ⊑ₑ-proof 𝑓′ con𝑓′ x y) →
                   (∀ {x y} → (x , y) ∈ 𝑓′ → iszeroprop x y) →
                   ∀ {x y} → (x , y) ∈ 𝑓 → iszeroprop x y
iszero↦-↓closed' p₁ p₂ xy∈𝑓 with (p₁ xy∈𝑓)
iszero↦-↓closed' p₁ p₂ xy∈𝑓
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
  }
  with (iszeroLemma {sub} {preable} {postable}
       (λ xy∈sub → p₂ (sub⊆𝑓 xy∈sub)))
iszero↦-↓closed' p₁ p₂ xy∈𝑓
  | record { y⊑post = y⊑post }
  | izprop₁ post⊑⊥
  = izprop₁ (NbhSys.⊑-trans Bool y⊑post post⊑⊥)
iszero↦-↓closed' p₁ p₂ xy∈𝑓
  | record { y⊑post = ⊑b-intro₁ }
  | izprop₂ 0⊑pre t⊑post
  = izprop₁ ⊑b-intro₁
iszero↦-↓closed' p₁ p₂ xy∈𝑓
  | record { y⊑post = ⊑b-intro₂ ; pre⊑x = pre⊑x }
  | izprop₂ 0⊑pre t⊑post
  = izprop₂ 0⊑x t⊑post
  where 0⊑x = NbhSys.⊑-trans Nat 0⊑pre pre⊑x
iszero↦-↓closed' p₁ p₂ xy∈𝑓
  | record { y⊑post = ⊑b-intro₁ }
  | izprop₃ s⊥⊑pre f⊑post
  = izprop₁ ⊑b-intro₁
iszero↦-↓closed' p₁ p₂ xy∈𝑓
  | record { y⊑post = ⊑b-intro₂ ; pre⊑x = pre⊑x }
  | izprop₃ s⊥⊑pre f⊑post
  = izprop₃ s⊥⊑x f⊑post
  where s⊥⊑x = NbhSys.⊑-trans Nat s⊥⊑pre pre⊑x

iszero↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑ₑ z →
                  𝑥 iszero↦ z → 𝑥 iszero↦ y
iszero↦-↓closed ⊑ₑ-intro₁ iszero↦-intro₁ = iszero↦-intro₁
iszero↦-↓closed ⊑ₑ-intro₁ (iszero↦-intro₂ _) = iszero↦-intro₁
iszero↦-↓closed (⊑ₑ-intro₂ con𝑓 _ p₁) (iszero↦-intro₂ p₂)
  = iszero↦-intro₂ (iszero↦-↓closed' p₁ p₂)

iszero↦-↑directed' : ∀ {𝑓 𝑓′} →
                     (∀ {x y} → (x , y) ∈ 𝑓 → iszeroprop x y) →
                     (∀ {x y} → (x , y) ∈ 𝑓′ → iszeroprop x y) →
                     ∀ {x y} → (x , y) ∈ (𝑓 ∪ 𝑓′) →
                     iszeroprop x y
iszero↦-↑directed' {𝑓} p₁ p₂ xy∈∪ with (∪-lemma₂ {𝑓 = 𝑓} xy∈∪)
... | inl xy∈𝑓 = p₁ xy∈𝑓
... | inr xy∈𝑓′ = p₂ xy∈𝑓′

iszero↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} →
                    𝑥 iszero↦ y → 𝑥 iszero↦ z →
                    ∀ conyz → 𝑥 iszero↦ (y ⊔ₑ z [ conyz ])
iszero↦-↑directed iszero↦-intro₁ iszero↦-intro₁ _
  = iszero↦-intro₁
iszero↦-↑directed iszero↦-intro₁ (iszero↦-intro₂ p) _
  = iszero↦-intro₂ p
iszero↦-↑directed (iszero↦-intro₂ p) iszero↦-intro₁ _
  = iszero↦-intro₂ p
iszero↦-↑directed (iszero↦-intro₂ p₁) (iszero↦-intro₂ p₂) (con-∪ _ _ _)
  = iszero↦-intro₂ (iszero↦-↑directed' p₁ p₂)

iszero↦-con'' : ∀ {x y x′ y′} →
                iszeroprop x y → iszeroprop x′ y′ →
                NbhSys.Con Nat x x′ →
                NbhSys.Con Bool y y′
iszero↦-con'' (izprop₁ ⊑b-intro₁) _ _
  = NbhSys.Con-⊔ Bool (NbhSys.⊑-⊥ Bool) (NbhSys.⊑-refl Bool)
iszero↦-con'' (izprop₁ ⊑b-intro₂) _ _
  = NbhSys.Con-⊔ Bool (NbhSys.⊑-⊥ Bool) (NbhSys.⊑-refl Bool)
iszero↦-con'' (izprop₂ _ _) (izprop₁ y′⊑⊥) _
  = NbhSys.Con-⊔ Bool (NbhSys.⊑-refl Bool) y′⊑t
  where y′⊑t = NbhSys.⊑-trans Bool y′⊑⊥ (NbhSys.⊑-⊥ Bool)
iszero↦-con'' (izprop₃ _ _) (izprop₁ y′⊑⊥) _
  = NbhSys.Con-⊔ Bool (NbhSys.⊑-refl Bool) y′⊑t
  where y′⊑t = NbhSys.⊑-trans Bool y′⊑⊥ (NbhSys.⊑-⊥ Bool)
iszero↦-con'' (izprop₂ x ⊑b-intro₂) (izprop₂ x₃ ⊑b-intro₂) x₂
  = conb-refl
iszero↦-con'' (izprop₂ ⊑ₙ-intro₂ ⊑b-intro₂)
  (izprop₃ (⊑ₙ-intro₃ _) ⊑b-intro₂) ()
iszero↦-con'' (izprop₃ (⊑ₙ-intro₃ _) ⊑b-intro₂)
  (izprop₂ ⊑ₙ-intro₂ ⊑b-intro₂) ()
iszero↦-con'' (izprop₃ (⊑ₙ-intro₃ _) ⊑b-intro₂)
  (izprop₃ (⊑ₙ-intro₃ _) ⊑b-intro₂) _
  = conb-refl

iszero↦-con' : ∀ {𝑔} →
               (∀ {x y} → (x , y) ∈ 𝑔 → iszeroprop x y) →
               Preable 𝑔 → Postable 𝑔
iszero↦-con' {∅} _ _ = post-nil
iszero↦-con' {(x , y) ∷ 𝑔} p (pre-cons preable𝑔 conxpre𝑔)
  with (p here) | iszeroLemma {preable = preable𝑔} {rec}
                  λ xy∈𝑔 → p (there xy∈𝑔)
  where rec = iszero↦-con' (λ xy∈𝑔 → p (there xy∈𝑔)) preable𝑔
... | zp₁ | zp₂ = post-cons rec (iszero↦-con'' zp₁ zp₂ conxpre𝑔)
  where rec = iszero↦-con' (λ xy∈𝑔 → p (there xy∈𝑔)) preable𝑔

iszero↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
              𝑥 iszero↦ y → 𝑥′ iszero↦ y′ →
              ValCon _ 𝑥 𝑥′ → ArrCon y y′
iszero↦-con iszero↦-intro₁ iszero↦-intro₁ _
  = conₑ-⊥₁
iszero↦-con (iszero↦-intro₂ x) iszero↦-intro₁ _
  = conₑ-⊥₁
iszero↦-con iszero↦-intro₁ (iszero↦-intro₂ _) _
  = conₑ-⊥₂
iszero↦-con (iszero↦-intro₂ p₁) (iszero↦-intro₂ p₂) _
  = con-∪ _ _ (cff λ 𝑔⊆∪ preable𝑔 →
    iszero↦-con' (λ xy∈𝑔 → iz𝑔 (𝑔⊆∪ xy∈𝑔)) preable𝑔)
  where iz𝑔 = iszero↦-↑directed' p₁ p₂
