{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.lamSub (𝐴 𝐵 : Ty) where

open import Appmap.Equivalence
open import Base.FinFun
open import Base.Variables hiding (𝐴 ; 𝐵)
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.lam.Instance
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation
open import Scwf.DomainScwf.Comprehension.p.Instance
open import Scwf.DomainScwf.Comprehension.p.Relation
open import Scwf.DomainScwf.Comprehension.q.Instance
open import Scwf.DomainScwf.Comprehension.q.Relation

private
  variable
    γ : tAppmap Δ Γ
    𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ]

lamSubLemma₁' : ∀ 𝑥 𝑓 → ∀ {con𝑓} →
                [ lam 𝑡 ∘ γ ] 𝑥 ↦ ⟪ 𝐹 𝑓 con𝑓 ⟫ →
                ∀ x y → < x , y > ∈ 𝑓 →
                [ 𝑡 ∘ ⟨ γ ∘ (p Δ 𝐴) , q Δ 𝐴 ⟩ ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫
lamSubLemma₁' {Δ = Δ} 𝑥 _
  (∘↦-intro _ 𝑦 _ γ𝑥↦𝑦 (lam↦-intro₂ _ _ 𝑓' p)) x y xy∈𝑓
  = ∘↦-intro ⟪ x , 𝑥 ⟫ ⟪ x , 𝑦 ⟫ ⟪ y ⟫ γ∘pq↦ (p x y xy∈𝑓)
  where q↦ = q↦-intro ⟪ x , 𝑥 ⟫ ⟪ x ⟫ (NbhSys.⊑-refl 𝐴)
        p↦𝑥 = p↦-intro ⟪ x , 𝑥 ⟫ 𝑥
              (NbhSys.⊑-refl (ValNbhSys _))
        γ∘p↦ = ∘↦-intro ⟪ x , 𝑥 ⟫ 𝑥 𝑦 p↦𝑥 γ𝑥↦𝑦
        γ∘pq↦ = ⟨⟩↦-intro ⟪ x , 𝑥 ⟫ ⟪ x , 𝑦 ⟫ γ∘p↦ q↦

lamSubLemma₁ : ∀ 𝑥 𝑦 → [ lam 𝑡 ∘ γ ] 𝑥 ↦ 𝑦 →
               [ lam (𝑡 ∘ ⟨ (γ ∘ p Δ 𝐴) , q Δ 𝐴 ⟩) ] 𝑥 ↦ 𝑦
lamSubLemma₁ {𝑡 = 𝑡} {Δ = Δ} {γ = γ} 𝑥 ⟪ ⊥ₑ , ⟪⟫ ⟫
  (∘↦-intro _ 𝑓' _ γ𝑥↦𝑓' lam𝑓'↦𝑓)
  = Appmap.↦-bottom (lam (𝑡 ∘ ⟨ (γ ∘ p Δ 𝐴) , q Δ 𝐴 ⟩))
lamSubLemma₁ 𝑥 ⟪ 𝐹 𝑓 con𝑓 , ⟪⟫ ⟫ (∘↦-intro _ 𝑓' _ γ𝑥↦𝑓' lam𝑓'↦𝑓)
  = lam↦-intro₂ 𝑥 𝑓 _ (lamSubLemma₁' 𝑥 𝑓 lam𝑥↦𝑓)
  where lam𝑥↦𝑓 = ∘↦-intro 𝑥 𝑓' ⟪ 𝐹 𝑓 con𝑓 ⟫ γ𝑥↦𝑓' lam𝑓'↦𝑓

-- From a proof that 𝑡 ∘ ⟨ (γ ∘ p Δ 𝐴) , q Δ 𝐴 ⟩ maps
-- 𝑥 to ⟪ 𝐹 𝑓 ⟫, we can find a valuation 𝑦 such that
-- γ maps 𝑥 to 𝑦, and 𝑡 maps ⟪ x , 𝑦 ⟫ to ⟪ y ⟫ for any
-- < x , y > ∈ 𝑓.
record P-Struct (γ : tAppmap Δ Γ) (𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ])
                (𝑥 : Valuation Δ) (𝑓 : NbhFinFun 𝐴 𝐵) :
                Set where
  field
    𝑦 : Valuation Γ
    γ𝑥↦𝑦 : [ γ ] 𝑥 ↦ 𝑦
    λ𝑡𝑦 : ∀ x y → < x , y > ∈ 𝑓 → [ 𝑡 ] ⟪ x , 𝑦 ⟫ ↦ ⟪ y ⟫

getP-Struct' : {γ : tAppmap Δ Γ} →
               ∀ 𝑥 x y 𝑦 𝑧 → (𝑓 : NbhFinFun 𝐴 𝐵) →
               ∀ {con𝑦𝑧 conxy𝑓} →
               [ 𝑡 ∘ ⟨ γ ∘ p Δ 𝐴 , q Δ 𝐴 ⟩ ] 𝑥 lam↦
               ⟪ 𝐹 (< x , y > ∷ 𝑓) conxy𝑓 ⟫ →
               [ 𝑡 ] ⟪ x , 𝑦 ⟫ ↦ ⟪ y ⟫ →
               (∀ x′ y′ → < x′ , y′ > ∈ 𝑓 →
               [ 𝑡 ] ⟪ x′ , 𝑧 ⟫ ↦ ⟪ y′ ⟫) →
               ∀ x′ y′ → < x′ , y′ > ∈ (< x , y > ∷ 𝑓) →
               [ 𝑡 ] ⟪ x′ , 𝑦 ⊔ᵥ 𝑧 [ con𝑦𝑧 ] ⟫ ↦ ⟪ y′ ⟫
getP-Struct' {Γ = Γ} {𝑡 = 𝑡}
  𝑥 x y 𝑦 𝑧 𝑓 {con𝑦𝑧} _ 𝑡x𝑦↦y _ _ _ here
  = Appmap.↦-mono 𝑡 x𝑦⊑x⊔ 𝑡x𝑦↦y
  where 𝑦⊑⊔ = NbhSys.⊑-⊔-fst (ValNbhSys _) con𝑦𝑧
        x𝑦⊑x⊔ = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ x , 𝑦 ⟫
                ⟪ x , 𝑦 ⊔ᵥ 𝑧 [ con𝑦𝑧 ] ⟫
                (NbhSys.⊑-refl 𝐴) 𝑦⊑⊔
getP-Struct' {Γ = Γ} {𝑡 = 𝑡}
  𝑥 x y 𝑦 𝑧 𝑓 {con𝑦𝑧} _ _ p x′ y′ (there x′y′∈𝑓)
  = Appmap.↦-mono 𝑡 x′r⊑x′⊔ (p x′ y′ x′y′∈𝑓)
  where r⊑⊔ = NbhSys.⊑-⊔-snd (ValNbhSys _) con𝑦𝑧
        x′r⊑x′⊔ = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ x′ , 𝑧 ⟫
                  ⟪ x′ , 𝑦 ⊔ᵥ 𝑧 [ con𝑦𝑧 ] ⟫
                  (NbhSys.⊑-refl 𝐴) r⊑⊔

getP-Struct : {γ : tAppmap Δ Γ} →
              ∀ 𝑥 → (𝑓 : NbhFinFun 𝐴 𝐵) → ∀ {con𝑓} →
              [ 𝑡 ∘ ⟨ γ ∘ p Δ 𝐴 , q Δ 𝐴 ⟩ ] 𝑥 lam↦ ⟪ 𝐹 𝑓 con𝑓 ⟫ →
              P-Struct γ 𝑡 𝑥 𝑓
getP-Struct {Γ = Γ} {𝑡 = 𝑡} {γ = γ} 𝑥 ∅ _
  = record { 𝑦 = ⊥ᵥ
           ; γ𝑥↦𝑦 = Appmap.↦-bottom γ
           ; λ𝑡𝑦 = λ x y → xy∈∅-abs
           }
getP-Struct 𝑥 (< x , y > ∷ 𝑓) (lam↦-intro₂ _ _ _ p)
  with (p x y here)
getP-Struct {Γ = Γ} {𝑡 = 𝑡} {γ = γ} 𝑥 (< x , y > ∷ 𝑓)
  {con𝑓 = con𝑓} (lam↦-intro₂ _ _ _ p)
  | ∘↦-intro _ ⟪ z , 𝑧 ⟫ _ (⟨⟩↦-intro _ _
    (∘↦-intro _ 𝑦 _ (p↦-intro _ _ 𝑦⊑𝑥) γ𝑦↦𝑧)
    (q↦-intro _ _ z⊑x)) 𝑡z𝑧↦y
  = record { 𝑦 = big⊔
           ; γ𝑥↦𝑦 = Appmap.↦-↑directed γ γ𝑥↦𝑧 rec-γ𝑥↦𝑦 con𝑧rec𝑦
           ; λ𝑡𝑦 = getP-Struct' 𝑥 x y 𝑧 rec-𝑦 𝑓 {conxy𝑓 = con𝑓}
                   (lam↦-intro₂ 𝑥 (< x , y > ∷ 𝑓) _ p)
                   𝑡x𝑧↦y rec-λ𝑡𝑦
           }
  where rec = getP-Struct {𝑡 = 𝑡} {γ = γ} 𝑥 𝑓
              {subsetIsCon con𝑓 ⊆-lemma₃}
              (lam↦-intro₂ 𝑥 𝑓 _ λ x′ y′ x′y′∈𝑓 →
              p x′ y′ (there x′y′∈𝑓))
        rec-𝑦 = P-Struct.𝑦 rec
        rec-γ𝑥↦𝑦 = P-Struct.γ𝑥↦𝑦 rec
        rec-λ𝑡𝑦 = P-Struct.λ𝑡𝑦 rec
        γ𝑥↦𝑧 = Appmap.↦-mono γ 𝑦⊑𝑥 γ𝑦↦𝑧
        z𝑧⊑x𝑧 = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ z , 𝑧 ⟫ ⟪ x , 𝑧 ⟫
                z⊑x (NbhSys.⊑-refl (ValNbhSys _))
        𝑡x𝑧↦y = Appmap.↦-mono 𝑡 z𝑧⊑x𝑧 𝑡z𝑧↦y
        con𝑦𝑥 = NbhSys.Con-⊔ (ValNbhSys _) 𝑦⊑𝑥
                (NbhSys.⊑-refl (ValNbhSys _))
        con𝑧rec𝑦 = Appmap.↦-con γ γ𝑦↦𝑧 rec-γ𝑥↦𝑦 con𝑦𝑥
        big⊔ = 𝑧 ⊔ᵥ rec-𝑦 [ con𝑧rec𝑦 ]

lamSubLemma₂ : ∀ 𝑥 y →
               [ 𝑡 ∘ ⟨ (γ ∘ p Δ 𝐴) , q Δ 𝐴 ⟩ ] 𝑥 lam↦ y →
               [ lam 𝑡 ∘ γ ] 𝑥 ↦ y
lamSubLemma₂ {𝑡 = 𝑡} {γ = γ} 𝑥 _ lam↦-intro₁
  = Appmap.↦-bottom (lam 𝑡 ∘ γ)
lamSubLemma₂ 𝑥 _ (lam↦-intro₂ _ 𝑓 con𝑓 p)
  with (getP-Struct 𝑥 𝑓 {con𝑓 = con𝑓} (lam↦-intro₂ 𝑥 𝑓 _ p))
lamSubLemma₂ {𝑡 = 𝑡} {γ = γ} 𝑥 _ (lam↦-intro₂ _ 𝑓 _ p)
  | record { 𝑦 = 𝑦
           ; γ𝑥↦𝑦 = γ𝑥↦𝑦
           ; λ𝑡𝑦 = λ𝑡𝑦
           }
  = ∘↦-intro 𝑥 𝑦 ⟪ 𝐹 𝑓 _ ⟫ γ𝑥↦𝑦 (lam↦-intro₂ 𝑦 𝑓 _ λ𝑡𝑦)

lamSub : ∀ {Γ : Ctx n} → (γ : tAppmap Δ Γ) → ∀ 𝑡 →
         (lam 𝑡 ∘ γ) ≈ lam (𝑡 ∘ ⟨ (γ ∘ p Δ 𝐴) , q Δ 𝐴 ⟩)
lamSub γ 𝑡 = ≈-intro (≼-intro lamSubLemma₁)
             (≼-intro lamSubLemma₂)
