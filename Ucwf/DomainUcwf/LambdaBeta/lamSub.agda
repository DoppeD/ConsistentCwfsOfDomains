{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.lamSub where

open import Appmap.Equivalence
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
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

p : uAppmap (suc m) m
p {m} = p' (nToCtx m) UniType

q : uAppmap (suc m) 1
q {m} = q' (nToCtx m) UniType

private
  variable
    γ : uAppmap n m
    𝑡 : uAppmap (suc m) 1

  UT : NbhSys
  UT = UniType

lamSubLemma₁' : ∀ 𝑥 𝑓 → [ lam 𝑡 ∘ γ ] 𝑥 ↦ ⟪ λᵤ 𝑓 ⟫ →
                ∀ x y → < x , y >ₛ ∈ₛ 𝑓 →
                [ 𝑡 ∘ ⟨ γ ∘ p , q ⟩ ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
lamSubLemma₁' {𝑡 = 𝑡} {γ = γ} 𝑥 _ _ x ⊥ᵤ _
  = ∘↦-intro ⟪ x , 𝑥 ⟫ ⊥ᵥ ⟪ ⊥ᵤ ⟫ ⟨⟩⊥↦⊥ 𝑡⊥↦⊥
  where 𝑡⊥↦⊥ = Appmap.↦-bottom 𝑡
        px𝑥↦⊥ = p↦-intro ⟪ x , 𝑥 ⟫ 𝑥
                (NbhSys.⊑-refl (ValNbhSys _))
        γ𝑥↦⊥ = Appmap.↦-bottom γ
        γ∘px𝑥↦⊥ = ∘↦-intro ⟪ x , 𝑥 ⟫ 𝑥 ⊥ᵥ px𝑥↦⊥ γ𝑥↦⊥
        qx𝑥↦⊥ = Appmap.↦-bottom q
        ⟨⟩⊥↦⊥ = ⟨⟩↦-intro ⟪ x , 𝑥 ⟫ ⊥ᵥ γ∘px𝑥↦⊥ qx𝑥↦⊥
lamSubLemma₁' 𝑥 _ (∘↦-intro _ 𝑦 _ γ𝑥↦𝑦 (lam↦-intro₂ _ _ p))
  x (λᵤ 𝑔) xy∈𝑓
  = ∘↦-intro ⟪ x , 𝑥 ⟫ ⟪ x , 𝑦 ⟫ ⟪ λᵤ 𝑔 ⟫ γ∘pq↦
    (p x (λᵤ 𝑔) xy∈𝑓)
  where q↦ = q↦-intro ⟪ x , 𝑥 ⟫ ⟪ x ⟫ (NbhSys.⊑-refl UT)
        p↦𝑥 = p↦-intro ⟪ x , 𝑥 ⟫ 𝑥
              (NbhSys.⊑-refl (ValNbhSys _))
        γ∘p↦ = ∘↦-intro ⟪ x , 𝑥 ⟫ 𝑥 𝑦 p↦𝑥 γ𝑥↦𝑦
        γ∘pq↦ = ⟨⟩↦-intro ⟪ x , 𝑥 ⟫ ⟪ x , 𝑦 ⟫ γ∘p↦ q↦

lamSubLemma₁ : ∀ 𝑥 𝑦 → [ lam 𝑡 ∘ γ ] 𝑥 ↦ 𝑦 →
               [ lam (𝑡 ∘ ⟨ γ ∘ p , q ⟩) ] 𝑥 ↦ 𝑦
lamSubLemma₁ 𝑥 ⟪ ⊥ᵤ , ⟪⟫ ⟫ _ = lam↦-intro₁
lamSubLemma₁ 𝑥 ⟪ λᵤ 𝑓 , ⟪⟫ ⟫ (∘↦-intro _ 𝑦 _ γ𝑥↦𝑦 lam𝑡𝑦↦𝑓)
  = lam↦-intro₂ 𝑥 𝑓 (lamSubLemma₁' 𝑥 𝑓 lam𝑥↦𝑓)
  where lam𝑥↦𝑓 = ∘↦-intro 𝑥 𝑦 ⟪ λᵤ 𝑓 ⟫ γ𝑥↦𝑦 lam𝑡𝑦↦𝑓

record P-Struct (γ : uAppmap n m)
                (𝑡 : uAppmap (suc m) 1)
                (𝑥 : uValuation n) (𝑓 : FinFunₛ) :
                Set where
  field
    𝑦 : uValuation m
    γ𝑥↦𝑦 : [ γ ] 𝑥 ↦ 𝑦
    λ𝑡𝑦 : ∀ x y → < x , y >ₛ ∈ₛ 𝑓 →
          [ 𝑡 ] ⟪ x , 𝑦 ⟫ ↦ ⟪ y ⟫

getP-Struct' : ∀ 𝑥 x y 𝑦 𝑧 𝑓 →
               [ 𝑡 ∘ ⟨ γ ∘ p , q ⟩ ] 𝑥 lam↦ ⟪ λᵤ (< x , y >ₛ ∷ 𝑓) ⟫ →
               [ 𝑡 ] ⟪ x , 𝑦 ⟫ ↦ ⟪ y ⟫ →
               (∀ x′ y′ → < x′ , y′ >ₛ ∈ₛ 𝑓 →
               [ 𝑡 ] ⟪ x′ , 𝑧 ⟫ ↦ ⟪ y′ ⟫) →
               ∀ x′ y′ → < x′ , y′ >ₛ ∈ₛ (< x , y >ₛ ∷ 𝑓) →
               [ 𝑡 ] ⟪ x′ , 𝑦 ⊔ᵥ 𝑧 ⟫ ↦ ⟪ y′ ⟫
getP-Struct' {m} {𝑡 = 𝑡} 𝑥 x y 𝑦 𝑧 𝑓 _ 𝑡x𝑦↦y _ _ _ here
  = Appmap.↦-mono 𝑡 x𝑦⊑x⊔ 𝑡x𝑦↦y
  where 𝑦⊑⊔ = NbhSys.⊑-⊔-fst (ValNbhSys _)
        x𝑦⊑x⊔ = ⊑ᵥ-cons (nToCtx (suc m)) ⟪ x , 𝑦 ⟫
                ⟪ x , 𝑦 ⊔ᵥ 𝑧 ⟫ (NbhSys.⊑-refl UT) 𝑦⊑⊔
getP-Struct' {m} {𝑡 = 𝑡} 𝑥 x y 𝑦 𝑧 𝑓 _ _ p x′ y′
  (there x′y′∈𝑓)
  = Appmap.↦-mono 𝑡 x′r⊑x′⊔ (p x′ y′ x′y′∈𝑓)
  where r⊑⊔ = NbhSys.⊑-⊔-snd (ValNbhSys _)
        x′r⊑x′⊔ = ⊑ᵥ-cons (nToCtx (suc m)) ⟪ x′ , 𝑧 ⟫
                  ⟪ x′ , 𝑦 ⊔ᵥ 𝑧 ⟫ (NbhSys.⊑-refl UT)
                  r⊑⊔

getP-Struct : ∀ 𝑥 → (𝑓 : FinFunₛ) →
              [ 𝑡 ∘ ⟨ γ ∘ p , q ⟩ ] 𝑥 lam↦ ⟪ λᵤ 𝑓 ⟫ →
              P-Struct γ 𝑡 𝑥 𝑓
getP-Struct {m} {γ = γ} 𝑥 ∅ _
  = record { 𝑦 = ⊥ᵥ
           ; γ𝑥↦𝑦 = Appmap.↦-bottom γ
           ; λ𝑡𝑦 = λ x y → xy∈∅-abs
           }
getP-Struct 𝑥 (< x , y >ₛ ∷ 𝑓) (lam↦-intro₂ _ _ p)
  with (p x y here)
getP-Struct {m} {𝑡 = 𝑡} {γ = γ} 𝑥 (< x , y >ₛ ∷ 𝑓)
  (lam↦-intro₂ _ _ p)
  | ∘↦-intro _ ⟪ z , 𝑧 ⟫ _ (⟨⟩↦-intro _ _
    (∘↦-intro _ 𝑦 _ (p↦-intro _ _ 𝑦⊑𝑥) γ𝑦↦𝑧)
    (q↦-intro _ _ z⊑x)) 𝑡z𝑧↦y
  = record { 𝑦 = 𝑧 ⊔ᵥ rec-𝑦
           ; γ𝑥↦𝑦 = Appmap.↦-↑directed γ γ𝑥↦𝑧 rec-γ𝑥↦𝑦
           ; λ𝑡𝑦 = getP-Struct' 𝑥 x y 𝑧 rec-𝑦 𝑓
                   (lam↦-intro₂ 𝑥 (< x , y >ₛ ∷ 𝑓) p)
                   𝑡x𝑧↦y rec-λ𝑡𝑦
           }
  where rec = getP-Struct {𝑡 = 𝑡} {γ = γ} 𝑥 𝑓
              (lam↦-intro₂ 𝑥 𝑓 λ x′ y′ x′y′∈𝑓 → p x′ y′
              (there x′y′∈𝑓))
        rec-𝑦 = P-Struct.𝑦 rec
        rec-γ𝑥↦𝑦 = P-Struct.γ𝑥↦𝑦 rec
        rec-λ𝑡𝑦 = P-Struct.λ𝑡𝑦 rec
        γ𝑥↦𝑧 = Appmap.↦-mono γ 𝑦⊑𝑥 γ𝑦↦𝑧
        z𝑧⊑x𝑧 = ⊑ᵥ-cons (nToCtx (suc m)) ⟪ z , 𝑧 ⟫
                ⟪ x , 𝑧 ⟫ z⊑x (NbhSys.⊑-refl (ValNbhSys _))
        𝑡x𝑧↦y = Appmap.↦-mono 𝑡 z𝑧⊑x𝑧 𝑡z𝑧↦y
        big⊔ = 𝑧 ⊔ᵥ rec-𝑦

lamSubLemma₂ :  ∀ 𝑥 𝑦 → [ lam (𝑡 ∘ ⟨ γ ∘ p , q ⟩) ] 𝑥 ↦ 𝑦 →
                [ lam 𝑡 ∘ γ ] 𝑥 ↦ 𝑦
lamSubLemma₂ {m} {γ = γ} 𝑥 ⟪ ⊥ᵤ , ⟪⟫ ⟫ x
  = ∘↦-intro 𝑥 ⊥ᵥ ⟪ ⊥ᵤ ⟫ γ𝑥↦⊥ lam⊥→⊥
  where γ𝑥↦⊥ = Appmap.↦-bottom γ
        lam⊥→⊥ = lam↦-intro₁
lamSubLemma₂ 𝑥 ⟪ λᵤ 𝑓 , ⟪⟫ ⟫ (lam↦-intro₂ _ _ p)
  with (getP-Struct 𝑥 𝑓 (lam↦-intro₂ 𝑥 𝑓 p))
lamSubLemma₂ {𝑡 = 𝑡} {γ = γ} 𝑥 ⟪ λᵤ 𝑓 , ⟪⟫ ⟫ _
  | record { 𝑦 = 𝑦
           ; γ𝑥↦𝑦 = γ𝑥↦𝑦
           ; λ𝑡𝑦 = λ𝑡𝑦
           }
  = ∘↦-intro 𝑥 𝑦 ⟪ λᵤ 𝑓 , ⟪⟫ ⟫ γ𝑥↦𝑦 (lam↦-intro₂ 𝑦 𝑓 λ𝑡𝑦)

lamSub : (γ : uAppmap n m) → (𝑡 : uAppmap (suc m) 1) →
         (lam 𝑡 ∘ γ) ≈ lam (𝑡 ∘ ⟨ (γ ∘ p) , q ⟩)
lamSub γ 𝑡 = ≈-intro (≼-intro lamSubLemma₁)
             (≼-intro lamSubLemma₂)
