{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.lamSub where

open import Appmap.Equivalence
open import Appmap.Composition.Instance
open import Appmap.Composition.Relation
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation
open import Scwf.DomainScwf.Comprehension.p.Instance renaming (p to p')
open import Scwf.DomainScwf.Comprehension.p.Relation
open import Scwf.DomainScwf.Comprehension.q.Instance renaming (q to q')
open import Scwf.DomainScwf.Comprehension.q.Relation
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.lam.Instance
open import Ucwf.DomainUcwf.LambdaBeta.lam.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.DomainUcwf.UniType.SizedFinFun

open import Agda.Builtin.Nat

p : uSub (suc m) m
p {m} = p' (nToCtx m) UniType

q : uTerm (suc m)
q {m} = q' (nToCtx m) UniType

private
  variable
    γ : uSub n m
    𝑡 : uTerm (suc m)

lamSubLemma₁' : ∀ {𝑥 𝑓} → [ lam 𝑡 ∘ γ ] 𝑥 ↦ (λᵤ 𝑓) →
                ∀ {x y} → (x , y) ∈ₛ 𝑓 →
                [ 𝑡 ∘ ⟨ γ ∘ p , q ⟩ ] ⟪ x ,, 𝑥 ⟫ ↦ y
lamSubLemma₁' (∘↦-intro γ𝑥↦𝑦 (lam↦-intro₂ p)) xy∈𝑓
  = ∘↦-intro γ∘pq↦ (p xy∈𝑓)
  where q↦ = q↦-intro (NbhSys.⊑-refl UniType)
        p↦𝑥 = p↦-intro (NbhSys.⊑-refl (ValNbhSys _))
        γ∘p↦ = ∘↦-intro p↦𝑥 γ𝑥↦𝑦
        γ∘pq↦ = ⟨⟩↦-intro γ∘p↦ q↦

lamSubLemma₁ : ∀ {𝑥 y} → [ lam 𝑡 ∘ γ ] 𝑥 ↦ y →
               [ lam (𝑡 ∘ ⟨ γ ∘ p , q ⟩) ] 𝑥 ↦ y
lamSubLemma₁ {y = ⊥ᵤ} _ = lam↦-intro₁
lamSubLemma₁ {y = λᵤ 𝑓} (∘↦-intro γ𝑥↦𝑦 lam𝑡𝑦↦𝑓)
  = lam↦-intro₂ (lamSubLemma₁' lam𝑥↦𝑓)
  where lam𝑥↦𝑓 = ∘↦-intro γ𝑥↦𝑦 lam𝑡𝑦↦𝑓

record P-Struct (γ : uSub n m)
                (𝑡 : uTerm (suc m))
                (𝑥 : uValuation n) (𝑓 : FinFunₛ) :
                Set where
  field
    𝑦 : uValuation m
    γ𝑥↦𝑦 : [ γ ] 𝑥 ↦ 𝑦
    λ𝑡𝑦 : ∀ {x y} → (x , y) ∈ₛ 𝑓 → [ 𝑡 ] ⟪ x ,, 𝑦 ⟫ ↦ y

getP-Struct' : ∀ 𝑥 x y 𝑦 𝑧 𝑓 →
               [ 𝑡 ∘ ⟨ γ ∘ p , q ⟩ ] 𝑥 lam↦ (λᵤ ((x , y) ∷ 𝑓)) →
               [ 𝑡 ] ⟪ x ,, 𝑦 ⟫ ↦ y →
               (∀ {x′ y′} → (x′ , y′) ∈ₛ 𝑓 →
               [ 𝑡 ] ⟪ x′ ,, 𝑧 ⟫ ↦ y′) →
               ∀ {x′ y′} → (x′ , y′) ∈ₛ ((x , y) ∷ 𝑓) →
               [ 𝑡 ] ⟪ x′ ,, 𝑦 ⊔ᵥ 𝑧 [ valConAll ] ⟫ ↦ y′
getP-Struct' {m} {𝑡 = 𝑡} 𝑥 x y 𝑦 𝑧 𝑓 _ 𝑡x𝑦↦y _ here
  = Appmap.↦-mono 𝑡 x𝑦⊑x⊔ 𝑡x𝑦↦y
  where 𝑦⊑⊔ = NbhSys.⊑-⊔-fst (ValNbhSys _) valConAll
        x𝑦⊑x⊔ = ⊑ᵥ-cons (nToCtx (suc m))
                (NbhSys.⊑-refl UniType) 𝑦⊑⊔
getP-Struct' {m} {𝑡 = 𝑡} 𝑥 x y 𝑦 𝑧 𝑓 _ _ p
  (there x′y′∈𝑓)
  = Appmap.↦-mono 𝑡 x′r⊑x′⊔ (p x′y′∈𝑓)
  where r⊑⊔ = NbhSys.⊑-⊔-snd (ValNbhSys _) valConAll
        x′r⊑x′⊔ = ⊑ᵥ-cons (nToCtx (suc m))
                  (NbhSys.⊑-refl UniType) r⊑⊔

getP-Struct : ∀ 𝑥 → (𝑓 : FinFunₛ) →
              [ 𝑡 ∘ ⟨ γ ∘ p , q ⟩ ] 𝑥 lam↦ (λᵤ 𝑓) →
              P-Struct γ 𝑡 𝑥 𝑓
getP-Struct {m} {γ = γ} 𝑥 ∅ _
  = record { 𝑦 = ⊥ᵥ
           ; γ𝑥↦𝑦 = Appmap.↦-bottom γ
           ; λ𝑡𝑦 = xy∈∅-abs
           }
getP-Struct 𝑥 ((x , y) ∷ 𝑓) (lam↦-intro₂ p)
  with (p here)
getP-Struct {m} {𝑡 = 𝑡} {γ = γ} 𝑥 ((x , y) ∷ 𝑓)
  (lam↦-intro₂ p)
  | ∘↦-intro {y = ⟪ z ,, 𝑧 ⟫}
    (⟨⟩↦-intro (∘↦-intro (p↦-intro 𝑦⊑𝑥) γ𝑦↦𝑧)
    (q↦-intro z⊑x)) 𝑡z𝑧↦y
  = record { 𝑦 = 𝑧 ⊔ᵥ rec-𝑦 [ valConAll ]
           ; γ𝑥↦𝑦 = Appmap.↦-↑directed γ γ𝑥↦𝑧 rec-γ𝑥↦𝑦 valConAll
           ; λ𝑡𝑦 = getP-Struct' 𝑥 x y 𝑧 rec-𝑦 𝑓 (lam↦-intro₂ p)
                   𝑡x𝑧↦y rec-λ𝑡𝑦
           }
  where rec = getP-Struct {𝑡 = 𝑡} {γ = γ} 𝑥 𝑓
              (lam↦-intro₂ λ x′y′∈𝑓 → p (there x′y′∈𝑓))
        rec-𝑦 = P-Struct.𝑦 rec
        rec-γ𝑥↦𝑦 = P-Struct.γ𝑥↦𝑦 rec
        rec-λ𝑡𝑦 = P-Struct.λ𝑡𝑦 rec
        γ𝑥↦𝑧 = Appmap.↦-mono γ 𝑦⊑𝑥 γ𝑦↦𝑧
        z𝑧⊑x𝑧 = ⊑ᵥ-cons (nToCtx (suc m)) z⊑x
                (NbhSys.⊑-refl (ValNbhSys _))
        𝑡x𝑧↦y = Appmap.↦-mono 𝑡 z𝑧⊑x𝑧 𝑡z𝑧↦y
        big⊔ = 𝑧 ⊔ᵥ rec-𝑦 [ valConAll ]

lamSubLemma₂ :  ∀ {𝑥 𝑦} → [ lam (𝑡 ∘ ⟨ γ ∘ p , q ⟩) ] 𝑥 ↦ 𝑦 →
                [ lam 𝑡 ∘ γ ] 𝑥 ↦ 𝑦
lamSubLemma₂ {m} {γ = γ} {𝑦 = ⊥ᵤ} _
  = ∘↦-intro γ𝑥↦⊥ lam⊥→⊥
  where γ𝑥↦⊥ = Appmap.↦-bottom γ
        lam⊥→⊥ = lam↦-intro₁
lamSubLemma₂ {𝑦 = λᵤ 𝑓} (lam↦-intro₂ p)
  with (getP-Struct _ _ (lam↦-intro₂ p))
lamSubLemma₂ {𝑡 = 𝑡} {γ = γ} {𝑦 = λᵤ 𝑓} _
  | record { 𝑦 = 𝑦
           ; γ𝑥↦𝑦 = γ𝑥↦𝑦
           ; λ𝑡𝑦 = λ𝑡𝑦
           }
  = ∘↦-intro γ𝑥↦𝑦 (lam↦-intro₂ λ𝑡𝑦)

lamSub : (γ : uSub n m) → (𝑡 : uTerm (suc m)) →
         (lam 𝑡 ∘ γ) ≈ lam (𝑡 ∘ ⟨ (γ ∘ p) , q ⟩)
lamSub γ 𝑡 = ≈-intro (≼-intro lamSubLemma₁)
             (≼-intro lamSubLemma₂)
