{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.iszeroeq2 where

open import Appmap.Definition
open import Appmap.Equivalence
open import Appmap.PrincipalIdeal.Relation
open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.NbhSys.Relation
open import PCF.DomainPCF.Bool.false.Instance
open import PCF.DomainPCF.Functions.iszero.Instance
open import PCF.DomainPCF.Functions.iszero.Lemmata
open import PCF.DomainPCF.Functions.iszero.Relation
open import PCF.DomainPCF.Functions.suc.Instance
open import PCF.DomainPCF.Functions.suc.Lemmata
open import PCF.DomainPCF.Functions.suc.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Bool
import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Nat
  as RelNN
import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Nat
  as CFFNN

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
  where izp = iszeroLemma {sub} {preable} {postable}
              (λ xy∈sub → p₁ (sub⊆𝑓 xy∈sub))

iszeroeq₂Lemma₁ : ∀ {n} → {𝑥 : Valuation Γ} → ∀ {y} →
                  [ ap iszero (ap suc n) ] 𝑥 ↦ y →
                  [ false ] 𝑥 ↦ y
iszeroeq₂Lemma₁ (ap↦-intro₁ y⊑⊥)
  = ideal↦-intro y⊑f
  where y⊑f = NbhSys.⊑-trans Bool y⊑⊥ (NbhSys.⊑-⊥ Bool)
iszeroeq₂Lemma₁
  (ap↦-intro₂ _ _ (iszero↦-intro₂ p) (ap↦-intro₁ x⊑⊥) xy⊑𝑓)
  = ideal↦-intro (iszeroeq₂Lemma₁' {n = ⊥ₙ} p x⊑sn xy⊑𝑓)
  where x⊑sn = NbhSys.⊑-trans Nat x⊑⊥ (NbhSys.⊑-⊥ Nat)
iszeroeq₂Lemma₁ (ap↦-intro₂ _ _ (iszero↦-intro₂ _)
  (ap↦-intro₂ _ _ _ _ (RelNN.⊑ₑ-intro₂ _ _ p₃)) _)
  with (p₃ here)
iszeroeq₂Lemma₁ (ap↦-intro₂ _ _ (iszero↦-intro₂ p₁)
  (ap↦-intro₂ {x = x} _ _ (suc↦-intro₂ p₂) _ _) xy⊑𝑓)
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = ideal↦-intro (iszeroeq₂Lemma₁' {n = x} p₁ y⊑sx xy⊑𝑓)
  where spre⊑sx = ⊑ₙ-intro₃ pre⊑x
        post⊑sx = NbhSys.⊑-trans Nat (sucLemma {sub} {preable}
                  λ xy∈sub → p₂ (sub⊆𝑓 xy∈sub)) spre⊑sx
        y⊑sx = NbhSys.⊑-trans Nat y⊑post post⊑sx

iszeroeq₂Lemma₂'' : ∀ {x y} → (x , y) ∈ ((⊥ₙ , sₙ ⊥ₙ) ∷ ∅) →
                    [ Nat ] y ⊑ sₙ x
iszeroeq₂Lemma₂'' here
  = ⊑ₙ-intro₃ ⊑ₙ-intro₁

iszeroeq₂Lemma₂' : ∀ {n x y} → (x , y) ∈ ((sₙ n , f) ∷ ∅) →
                   iszeroprop x y
iszeroeq₂Lemma₂' here
  = izprop₃ (⊑ₙ-intro₃ ⊑ₙ-intro₁) (NbhSys.⊑-refl Bool)

iszeroeq₂Lemma₂ : ∀ {n} → {𝑥 : Valuation Γ} → ∀ {y} →
                  [ false ] 𝑥 ↦ y →
                  [ ap iszero (ap suc n) ] 𝑥 ↦ y
iszeroeq₂Lemma₂ (ideal↦-intro ⊑b-intro₁)
  = ap↦-intro₁ (NbhSys.⊑-⊥ Bool)
iszeroeq₂Lemma₂ {n = n} (ideal↦-intro ⊑b-intro₂)
  = ap↦-intro₂ cons⊥f cons⊥f iz𝑥↦s⊥f aps⊥𝑥↦sn s⊥f⊑s⊥f
  where iz𝑥↦s⊥f = iszero↦-intro₂ iszeroeq₂Lemma₂'
        n𝑥↦⊥ = Appmap.↦-bottom n
        s⊥s⊥⊑s⊥s⊥ = NbhSys.⊑-refl (Nat ⇒ Nat)
        suc𝑥↦⊥s⊥ = suc↦-intro₂ iszeroeq₂Lemma₂''
        con⊥s⊥ = CFFNN.singletonIsCon
        cons⊥f = singletonIsCon
        aps⊥𝑥↦sn = ap↦-intro₂ con⊥s⊥ con⊥s⊥ suc𝑥↦⊥s⊥ n𝑥↦⊥ s⊥s⊥⊑s⊥s⊥
        s⊥f⊑s⊥f = NbhSys.⊑-refl (Nat ⇒ Bool)

iszeroeq₂ : ∀ {n} → ap {Γ = Γ} iszero (ap suc n) ≈ false
iszeroeq₂ = ≈-intro (≼-intro iszeroeq₂Lemma₁)
            (≼-intro iszeroeq₂Lemma₂)
