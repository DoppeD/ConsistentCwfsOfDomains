{-# OPTIONS --safe #-}

module PCF.DomainPCF.Bool.iszeroeq2 where

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
open import PCF.DomainPCF.Bool.false.Instance
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

open import Agda.Builtin.Nat
  renaming (Nat to AgdaNat ; suc to AgdaSuc)
  hiding (zero)

iszeroeq₂Lemma₁'' : ∀ {n x y x′ y′} → [ Nat ] x ⊑ sₙ n →
                    [ Nat ] x′ ⊑ x → [ Bool ] y ⊑ y′ →
                    iszeroprop x′ y′ →
                    [ Bool ] y ⊑ f
iszeroeq₂Lemma₁'' _ _ y⊑y′ (izprop₁ y′⊑⊥)
  = NbhSys.⊑-trans Bool y⊑y′ y′⊑f
  where y′⊑f = NbhSys.⊑-trans Bool y′⊑⊥ ⊑b-intro₁
iszeroeq₂Lemma₁'' _ _ ⊑b-intro₁ (izprop₂ _ ⊑b-intro₂)
  = ⊑b-intro₁
iszeroeq₂Lemma₁'' () ⊑ₙ-intro₂ ⊑b-intro₂ (izprop₂ ⊑ₙ-intro₂ ⊑b-intro₂)
iszeroeq₂Lemma₁'' _ _ y⊑y′ (izprop₃ _ ⊑b-intro₂)
  = y⊑y′

iszeroeq₂Lemma₁' : ∀ {n x y 𝑓 con𝑓 conxy} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → iszeroprop x y) →
                   [ Nat ] x ⊑ sₙ n →
                   [ Nat ⇒ Bool ]
                     (𝐹 ((x , y) ∷ ∅) conxy) ⊑ 𝐹 𝑓 con𝑓 →
                   [ Bool ] y ⊑ f
iszeroeq₂Lemma₁' _ _ (⊑ₑ-intro₂ _ _ p₂) with (p₂ here)
iszeroeq₂Lemma₁' p₁ x⊑sn _ _
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = iszeroeq₂Lemma₁'' x⊑sn pre⊑x y⊑post izp
  where izp = iszero↦-↓closed'' {sub} {preable} {postable}
              (λ xy∈sub → p₁ (sub⊆𝑓 xy∈sub))

iszeroeq₂Lemma₁ : ∀ {n} → {𝑥 : Valuation Γ} → ∀ {y} →
                  [ ap iszero (num (AgdaSuc n)) ] 𝑥 ↦ y →
                  [ false ] 𝑥 ↦ y
iszeroeq₂Lemma₁ (ap↦-intro₁ y⊑⊥)
  = ideal↦-intro y⊑f
  where y⊑f = NbhSys.⊑-trans Bool y⊑⊥ (NbhSys.⊑-⊥ Bool)
iszeroeq₂Lemma₁
  (ap↦-intro₂ _ _ (iszero↦-intro₂ p) (ideal↦-intro x⊑sn) xy⊑𝑓)
  = ideal↦-intro (iszeroeq₂Lemma₁' p x⊑sn xy⊑𝑓)

iszeroeq₂Lemma₂' : ∀ {n x y} → (x , y) ∈ ((sₙ n , f) ∷ ∅) →
                   iszeroprop x y
iszeroeq₂Lemma₂' here
  = izprop₃ (⊑ₙ-intro₃ ⊑ₙ-intro₁) (NbhSys.⊑-refl Bool)

iszeroeq₂Lemma₂ : ∀ {n} → {𝑥 : Valuation Γ} → ∀ {y} →
                  [ false ] 𝑥 ↦ y →
                  [ ap iszero (num (AgdaSuc n)) ] 𝑥 ↦ y
iszeroeq₂Lemma₂ (ideal↦-intro ⊑b-intro₁)
  = ap↦-intro₁ (NbhSys.⊑-⊥ Bool)
iszeroeq₂Lemma₂ {n} (ideal↦-intro ⊑b-intro₂)
  = ap↦-intro₂ singletonIsCon singletonIsCon iz𝑥↦snf numsn𝑥↦sn snf⊑snf
  where nNbh = natToNbh n
        iz𝑥↦snf = iszero↦-intro₂ iszeroeq₂Lemma₂'
        numsn𝑥↦sn = ideal↦-intro (NbhSys.⊑-refl Nat)
        snf⊑snf = NbhSys.⊑-refl (Nat ⇒ Bool)

iszeroeq₂ : ∀ {n} → ap {Γ = Γ} iszero (num (AgdaSuc n)) ≈ false
iszeroeq₂ = ≈-intro (≼-intro iszeroeq₂Lemma₁)
            (≼-intro iszeroeq₂Lemma₂)
