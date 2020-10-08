{-# OPTIONS --safe #-}

module PCF.DomainPCF.Bool.iszeroeq1 where

open import Appmap.Definition
open import Appmap.Equivalence
open import Appmap.PrincipalIdeal.Relation
open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Bool.iszero.AxiomProofs
open import PCF.DomainPCF.Bool.iszero.Instance
open import PCF.DomainPCF.Bool.iszero.Relation
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.NbhSys.Relation
open import PCF.DomainPCF.Bool.true.Instance
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import PCF.DomainPCF.Nat.num.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Bool

iszeroeq₁Lemma₁'' : ∀ {x y x′ y′} → [ Nat ] x ⊑ 0ₙ →
                    [ Nat ] x′ ⊑ x → [ Bool ] y ⊑ y′ →
                    iszeroprop x′ y′ →
                    [ Bool ] y ⊑ t
iszeroeq₁Lemma₁'' _ _ y⊑y′ (izprop₁ y′⊑⊥)
  = NbhSys.⊑-trans Bool y⊑y′ y′⊑t
  where y′⊑t = NbhSys.⊑-trans Bool y′⊑⊥ ⊑b-intro₁
iszeroeq₁Lemma₁'' _ _ y⊑t (izprop₂ _ ⊑b-intro₂)
  = y⊑t
iszeroeq₁Lemma₁'' x x₁ ⊑b-intro₁ (izprop₃ x₃ ⊑b-intro₂)
  = ⊑b-intro₁
iszeroeq₁Lemma₁'' ⊑ₙ-intro₁ () ⊑b-intro₂
  (izprop₃ (⊑ₙ-intro₃ _) ⊑b-intro₂)
iszeroeq₁Lemma₁'' ⊑ₙ-intro₂ () ⊑b-intro₂
  (izprop₃ (⊑ₙ-intro₃ _) ⊑b-intro₂)

iszeroeq₁Lemma₁' : ∀ {x y 𝑓 con𝑓 conxy} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → iszeroprop x y) →
                   [ Nat ] x ⊑ 0ₙ →
                   [ Nat ⇒ Bool ]
                     (𝐹 ((x , y) ∷ ∅) conxy) ⊑ 𝐹 𝑓 con𝑓 →
                   [ Bool ] y ⊑ t
iszeroeq₁Lemma₁' _ _ (⊑ₑ-intro₂ _ _ p₂) with (p₂ here)
iszeroeq₁Lemma₁' p₁ x⊑0 _ _
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = iszeroeq₁Lemma₁'' x⊑0 pre⊑x y⊑post izp
  where izp = iszero↦-↓closed'' {sub} {preable} {postable}
              (λ xy∈sub → p₁ (sub⊆𝑓 xy∈sub))

iszeroeq₁Lemma₁ : {𝑥 : Valuation Γ} → ∀ {y} →
                  [ ap iszero (num 0) ] 𝑥 ↦ y →
                  [ true ] 𝑥 ↦ y
iszeroeq₁Lemma₁ (ap↦-intro₁ y⊑⊥)
  = ideal↦-intro y⊑t
  where y⊑t = NbhSys.⊑-trans Bool y⊑⊥ (NbhSys.⊑-⊥ Bool)
iszeroeq₁Lemma₁
  (ap↦-intro₂ _ _ (iszero↦-intro₂ p) (ideal↦-intro x⊑0) xy⊑𝑓)
  = ideal↦-intro (iszeroeq₁Lemma₁' p x⊑0 xy⊑𝑓)

iszeroeq₁Lemma₂' : ∀ {x y} → (x , y) ∈ ((0ₙ , t) ∷ ∅) →
                   iszeroprop x y
iszeroeq₁Lemma₂' here
  = izprop₂ (NbhSys.⊑-refl Nat) (NbhSys.⊑-refl Bool)

iszeroeq₁Lemma₂ : {𝑥 : Valuation Γ} → ∀ {y} →
                  [ true ] 𝑥 ↦ y →
                  [ ap iszero (num 0) ] 𝑥 ↦ y
iszeroeq₁Lemma₂ (ideal↦-intro ⊑b-intro₁)
  = ap↦-intro₁ (NbhSys.⊑-⊥ Bool)
iszeroeq₁Lemma₂ (ideal↦-intro ⊑b-intro₂)
  = ap↦-intro₂ singletonIsCon singletonIsCon iz𝑥↦0t num0𝑥↦0 0t⊑0t
  where iz𝑥↦0t = iszero↦-intro₂ iszeroeq₁Lemma₂'
        num0𝑥↦0 = ideal↦-intro (NbhSys.⊑-refl Nat)
        0t⊑0t = NbhSys.⊑-refl (Nat ⇒ Bool)

iszeroeq₁ : ap {Γ = Γ} iszero (num 0) ≈ true
iszeroeq₁ = ≈-intro (≼-intro iszeroeq₁Lemma₁)
            (≼-intro iszeroeq₁Lemma₂)
