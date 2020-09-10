{-# OPTIONS --safe #-}

module Scwf.DomainScwf.PlainAxiomProofs where

open import Appmap.Equivalence
open import Appmap.Lemmata
open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Appmap.Empty.Instance
open import Scwf.DomainScwf.Appmap.Empty.Relation
open import Scwf.DomainScwf.Appmap.Identity.Instance
open import Scwf.DomainScwf.Appmap.Identity.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.Comprehension.p.Instance
open import Scwf.DomainScwf.Comprehension.p.Relation
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation
open import Scwf.DomainScwf.Comprehension.q.Instance
open import Scwf.DomainScwf.Comprehension.q.Relation

private
  variable
    γ γ′ : tAppmap Γ Δ
    δ δ′ : tAppmap Δ Θ
    θ : tAppmap Θ Λ
    𝑡 𝑡′ : tAppmap Δ [ 𝐴 ]

subAssocLemma₁ : ∀ 𝑥 𝑦 → [ (θ ∘ δ) ∘ γ ] 𝑥 ↦ 𝑦 →
                 [ θ ∘ (δ ∘ γ) ] 𝑥 ↦ 𝑦
subAssocLemma₁ 𝑥 𝑦 (∘↦-intro _ 𝑧 _ γ𝑥↦𝑧
  (∘↦-intro _ 𝑤 _ δ𝑧↦𝑤 θ𝑤↦𝑦))
  = ∘↦-intro 𝑥 𝑤 𝑦 (∘↦-intro 𝑥 𝑧 𝑤 γ𝑥↦𝑧 δ𝑧↦𝑤) θ𝑤↦𝑦

subAssocLemma₂ : ∀ 𝑥 𝑦 → [ θ ∘ (δ ∘ γ) ] 𝑥 ↦ 𝑦 →
                 [ (θ ∘ δ) ∘ γ ] 𝑥 ↦ 𝑦
subAssocLemma₂ 𝑥 𝑦 (∘↦-intro _ 𝑧 _
  (∘↦-intro _ 𝑤 _₁ γ𝑥↦𝑤 δ𝑤↦𝑧) θ𝑧↦𝑦)
  = ∘↦-intro 𝑥 𝑤 𝑦 γ𝑥↦𝑤 (∘↦-intro 𝑤 𝑧 𝑦 δ𝑤↦𝑧 θ𝑧↦𝑦)

subAssoc : (γ : tAppmap Γ Δ) → (δ : tAppmap Δ Θ) →
           (θ : tAppmap Θ Λ) →
           ((θ ∘ δ) ∘ γ) ≈ (θ ∘ (δ ∘ γ))
subAssoc γ δ θ = ≈-intro (≼-intro subAssocLemma₁)
              (≼-intro subAssocLemma₂)

pConsLemma₁ : ∀ 𝑥 𝑦 → [ p Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦 →
              [ γ ] 𝑥 ↦ 𝑦
pConsLemma₁ {γ = γ} {𝑡 = 𝑡} 𝑥 𝑦 (∘↦-intro _ ⟪ z , 𝑧 ⟫ _
  (⟨⟩↦-intro _ _ γ𝑥↦𝑧 _) (p↦-intro _ _ 𝑦⊑𝑧))
  = Appmap.↦-↓closed γ 𝑦⊑𝑧 γ𝑥↦𝑧

pConsLemma₂ : ∀ 𝑥 𝑦 → [ γ ] 𝑥 ↦ 𝑦 →
              [ p Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦
pConsLemma₂ {γ = γ} {𝐴 = 𝐴} {𝑡} 𝑥 𝑦 γ𝑥↦𝑦
  = ∘↦-intro 𝑥 ⟪ NbhSys.⊥ 𝐴 , 𝑦 ⟫ 𝑦 γ𝑡𝑥↦⊥𝑦 p⊥𝑦↦𝑦
  where 𝑡𝑥↦⊥ = Appmap.↦-bottom 𝑡
        γ𝑡𝑥↦⊥𝑦 = ⟨⟩↦-intro 𝑥 ⟪ NbhSys.⊥ 𝐴 , 𝑦 ⟫ γ𝑥↦𝑦 𝑡𝑥↦⊥
        p⊥𝑦↦𝑦 = p↦-intro ⟪ NbhSys.⊥ 𝐴 , 𝑦 ⟫ 𝑦
                (NbhSys.⊑-refl (ValNbhSys _))

pCons : (γ : tAppmap Δ Γ) → (𝑡 : tAppmap Δ [ 𝐴 ]) →
        (p Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩) ≈ γ
pCons γ 𝑡 = ≈-intro (≼-intro pConsLemma₁)
            (≼-intro pConsLemma₂)

qConsLemma₁ : ∀ 𝑥 𝑦 → [ q Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦 →
              [ 𝑡 ] 𝑥 ↦ 𝑦
qConsLemma₁ {𝐴 = 𝐴} {𝑡 = 𝑡} 𝑥 ⟪ y , ⟪⟫ ⟫
  (∘↦-intro _ ⟪ z , _ ⟫ _ (⟨⟩↦-intro _ _ _ 𝑡𝑥↦z)
  (q↦-intro _ _ y⊑z))
  = Appmap.↦-↓closed 𝑡 tup-y⊑z 𝑡𝑥↦z
  where tup-y⊑z = ⊑ᵥ-cons [ 𝐴 ] ⟪ y ⟫ ⟪ z ⟫ y⊑z ⊑ᵥ-nil

qConsLemma₂ : ∀ 𝑥 𝑦 → [ 𝑡 ] 𝑥 ↦ 𝑦 →
              [ q Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦
qConsLemma₂ {𝐴 = 𝐴} {γ = γ} 𝑥 ⟪ y , ⟪⟫ ⟫ 𝑡𝑥↦y =
  ∘↦-intro 𝑥 ⟪ y , ⊥ᵥ ⟫ ⟪ y ⟫ γ𝑡𝑥↦y⊥ qy⊥↦y
  where γ𝑥↦⊥ = Appmap.↦-bottom γ
        qy⊥↦y = q↦-intro ⟪ y , ⊥ᵥ ⟫ ⟪ y ⟫
                (NbhSys.⊑-refl 𝐴)
        γ𝑡𝑥↦y⊥ = ⟨⟩↦-intro 𝑥 ⟪ y , ⊥ᵥ ⟫ γ𝑥↦⊥ 𝑡𝑥↦y

qCons : (γ : tAppmap Δ Γ) → (𝑡 : tAppmap Δ [ 𝐴 ]) →
        ((q Γ 𝐴) ∘ ⟨ γ , 𝑡 ⟩) ≈ 𝑡
qCons γ 𝑡 = ≈-intro (≼-intro qConsLemma₁)
            (≼-intro qConsLemma₂)

idExtLemma₁ : ∀ 𝑥 𝑦 → 𝑥 id↦ 𝑦 → ⟨⟩↦ (p Γ 𝐴) (q Γ 𝐴) 𝑥 𝑦
idExtLemma₁ ⟪ x , 𝑥 ⟫ ⟪ y , 𝑦 ⟫
  (id↦-intro _ _ (⊑ᵥ-cons _ _ _ y⊑x 𝑦⊑𝑥))
  = ⟨⟩↦-intro ⟪ x , 𝑥 ⟫ ⟪ y , 𝑦 ⟫ px𝑥↦𝑦 qx𝑥↦𝑦
  where px𝑥↦𝑦 = p↦-intro ⟪ x , 𝑥 ⟫ 𝑦 𝑦⊑𝑥
        qx𝑥↦𝑦 = q↦-intro ⟪ x , 𝑥 ⟫ ⟪ y ⟫ y⊑x

idExtLemma₂ : ∀ 𝑥 𝑦 → ⟨⟩↦ (p Γ 𝐴) (q Γ 𝐴) 𝑥 𝑦 →
              𝑥 id↦ 𝑦
idExtLemma₂ {Γ = Γ} {𝐴 = 𝐴} ⟪ x , 𝑥 ⟫ ⟪ y , 𝑦 ⟫
  (⟨⟩↦-intro _ _ (p↦-intro _ _ 𝑦⊑𝑥) (q↦-intro _ _ y⊑x))
  = id↦-intro ⟪ x , 𝑥 ⟫ ⟪ y , 𝑦 ⟫ y𝑦⊑x𝑥
  where y𝑦⊑x𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ y , 𝑦 ⟫ ⟪ x , 𝑥 ⟫ y⊑x 𝑦⊑𝑥

idExt : idMap (𝐴 :: Γ) ≈ ⟨ p Γ 𝐴 , q Γ 𝐴 ⟩
idExt = ≈-intro (≼-intro idExtLemma₁)
        (≼-intro idExtLemma₂) 

idLLemma₁ : ∀ 𝑥 𝑦 → [ idMap Γ ∘ γ ] 𝑥 ↦ 𝑦 →
            [ γ ] 𝑥 ↦ 𝑦
idLLemma₁ {Γ = Γ} {γ = γ} 𝑥 𝑦
  (∘↦-intro _ 𝑧 _ γ𝑥↦𝑧 (id↦-intro _ _ 𝑦⊑𝑧))
  = Appmap.↦-↓closed γ 𝑦⊑𝑧 γ𝑥↦𝑧

idLLemma₂ : ∀ 𝑥 𝑦 → [ γ ] 𝑥 ↦ 𝑦 →
            [ idMap Γ ∘ γ ] 𝑥 ↦ 𝑦
idLLemma₂ 𝑥 𝑦 𝑥↦𝑦 = ∘↦-intro 𝑥 𝑦 𝑦 𝑥↦𝑦 (id↦-intro 𝑦 𝑦 𝑦⊑𝑦)
   where 𝑦⊑𝑦 = NbhSys.⊑-refl (ValNbhSys _)

idL : (γ : tAppmap Δ Γ) → (idMap Γ ∘ γ) ≈ γ
idL γ = ≈-intro (≼-intro idLLemma₁) (≼-intro idLLemma₂)

idRLemma₁ : ∀ 𝑥 𝑦 → [ γ ∘ idMap Δ ] 𝑥 ↦ 𝑦 →
            [ γ ] 𝑥 ↦ 𝑦
idRLemma₁ {γ = γ} 𝑥 𝑦
  (∘↦-intro _ 𝑧 _ (id↦-intro _ _ 𝑧⊑𝑥) γ𝑧↦𝑦)
  = Appmap.↦-mono γ 𝑧⊑𝑥 γ𝑧↦𝑦

idRLemma₂ : ∀ 𝑥 𝑦 → [ γ ] 𝑥 ↦ 𝑦 →
            [ γ ∘ idMap Δ ] 𝑥 ↦ 𝑦
idRLemma₂ 𝑥 𝑦 𝑥↦𝑦
  = ∘↦-intro 𝑥 𝑥 𝑦 (id↦-intro 𝑥 𝑥 𝑥⊑𝑥) 𝑥↦𝑦
  where 𝑥⊑𝑥 = NbhSys.⊑-refl (ValNbhSys _)

idR : (γ : tAppmap Δ Γ) → (γ ∘ idMap Δ) ≈ γ
idR γ = ≈-intro (≼-intro idRLemma₁) (≼-intro idRLemma₂)

id₀Lemma₁ : ∀ 𝑥 𝑦 → 𝑥 id↦ 𝑦 → 𝑥 empty↦ 𝑦
id₀Lemma₁ ⟪⟫ ⟪⟫ id𝑥↦𝑦 = empty↦-intro

id₀Lemma₂ : ∀ 𝑥 𝑦 → 𝑥 empty↦ 𝑦 → 𝑥 id↦ 𝑦
id₀Lemma₂ ⟪⟫ ⟪⟫ em𝑥↦𝑦 = id↦-intro ⟪⟫ ⟪⟫ ⊑ᵥ-nil

id₀ : idMap [] ≈ emptyMap
id₀ = ≈-intro (≼-intro id₀Lemma₁) (≼-intro id₀Lemma₂)

<>-zeroLemma₁ : ∀ 𝑥 𝑦 → [ emptyMap ∘ γ ] 𝑥 ↦ 𝑦 →
                𝑥 empty↦ 𝑦
<>-zeroLemma₁ 𝑥 ⟪⟫ _ = empty↦-intro

<>-zeroLemma₂ : ∀ 𝑥 𝑦 → 𝑥 empty↦ 𝑦 →
                [ emptyMap ∘ γ ] 𝑥 ↦ 𝑦
<>-zeroLemma₂ {γ = γ} 𝑥 ⟪⟫ empty↦-intro
  = ∘↦-intro 𝑥 ⊥ᵥ ⟪⟫ γ𝑥↦⊥ empty↦-intro
    where γ𝑥↦⊥ = Appmap.↦-bottom γ

<>-zero : (γ : tAppmap Γ Δ) → (emptyMap ∘ γ) ≈ emptyMap
<>-zero γ = ≈-intro (≼-intro <>-zeroLemma₁)
            (≼-intro <>-zeroLemma₂)

idSubLemma₁ : ∀ 𝑥 𝑦 → [ 𝑡 ∘ idMap Γ ] 𝑥 ↦ 𝑦 →
              [ 𝑡 ] 𝑥 ↦ 𝑦
idSubLemma₁ {𝑡 = 𝑡} 𝑥 𝑦
  (∘↦-intro _ 𝑧 _ (id↦-intro _ _ 𝑧⊑𝑥) 𝑡𝑧↦𝑦)
  = Appmap.↦-mono 𝑡 𝑧⊑𝑥 𝑡𝑧↦𝑦

idSubLemma₂ : ∀ 𝑥 𝑦 → [ 𝑡 ] 𝑥 ↦ 𝑦 →
              [ 𝑡 ∘ idMap Γ ] 𝑥 ↦ 𝑦
idSubLemma₂ {Γ = Γ} {𝑡 = 𝑡} 𝑥 𝑦 𝑡𝑥↦𝑦
  = ∘↦-intro 𝑥 𝑥 𝑦 (id↦-intro 𝑥 𝑥 𝑥⊑𝑥) 𝑡𝑥↦𝑦
  where 𝑥⊑𝑥 = NbhSys.⊑-refl (ValNbhSys _)

idSub : (𝑡 : tAppmap Γ [ 𝐴 ]) →
        (𝑡 ∘ idMap Γ) ≈ 𝑡
idSub t = ≈-intro (≼-intro idSubLemma₁)
          (≼-intro idSubLemma₂)

compSubLemma₁ : ∀ 𝑥 𝑦 → [ 𝑡 ∘ (γ ∘ δ) ] 𝑥 ↦ 𝑦 →
                [ (𝑡 ∘ γ) ∘ δ ] 𝑥 ↦ 𝑦
compSubLemma₁ 𝑥 𝑦
  (∘↦-intro _ 𝑧 _ (∘↦-intro _ 𝑤 _ δ𝑥↦𝑤 γ𝑤↦𝑧) 𝑡𝑧↦𝑦)
  = ∘↦-intro 𝑥 𝑤 𝑦 δ𝑥↦𝑤 (∘↦-intro 𝑤 𝑧 𝑦 γ𝑤↦𝑧 𝑡𝑧↦𝑦)

compSubLemma₂ : ∀ 𝑥 𝑦 → [ (𝑡 ∘ γ) ∘ δ ] 𝑥 ↦ 𝑦 →
                [ 𝑡 ∘ (γ ∘ δ) ] 𝑥 ↦ 𝑦
compSubLemma₂ 𝑥 𝑦
  (∘↦-intro _ 𝑧 _ δ𝑥↦𝑧 (∘↦-intro _ 𝑤 _ γ𝑧↦𝑤 𝑡𝑤↦𝑦))
  = ∘↦-intro 𝑥 𝑤 𝑦 (∘↦-intro 𝑥 𝑧 𝑤 δ𝑥↦𝑧 γ𝑧↦𝑤) 𝑡𝑤↦𝑦

compSub : (𝑡 : tAppmap Δ [ 𝐴 ]) → (γ : tAppmap Γ Δ) →
          (δ : tAppmap Θ Γ) →
          (𝑡 ∘ (γ ∘ δ)) ≈ ((𝑡 ∘ γ) ∘ δ)
compSub 𝑡 γ δ = ≈-intro (≼-intro compSubLemma₁)
                (≼-intro compSubLemma₂)

compExtLemma₁ : ∀ 𝑥 𝑦 → [ ⟨ γ , 𝑡 ⟩ ∘ δ ] 𝑥 ↦ 𝑦 →
                [ ⟨ γ ∘ δ , 𝑡 ∘ δ ⟩ ] 𝑥 ↦ 𝑦
compExtLemma₁ 𝑥 ⟪ y , 𝑦 ⟫
  (∘↦-intro _ 𝑧 _ δ𝑥↦𝑧 (⟨⟩↦-intro _ _ γ𝑧↦𝑦 𝑡𝑧↦y))
  = ⟨⟩↦-intro 𝑥 ⟪ y , 𝑦 ⟫ (∘↦-intro 𝑥 𝑧 𝑦 δ𝑥↦𝑧 γ𝑧↦𝑦)
    (∘↦-intro 𝑥 𝑧 ⟪ y ⟫ δ𝑥↦𝑧 𝑡𝑧↦y)

compExtLemma₂ : ∀ 𝑥 𝑦 → [ ⟨ γ ∘ δ , 𝑡 ∘ δ ⟩ ] 𝑥 ↦ 𝑦 →
                [ ⟨ γ , 𝑡 ⟩ ∘ δ ] 𝑥 ↦ 𝑦
compExtLemma₂ {γ = γ} {δ = δ} {𝑡 = 𝑡} 𝑥 ⟪ y , 𝑦 ⟫
  (⟨⟩↦-intro _ _ (∘↦-intro _ 𝑧 _ δ𝑥↦𝑧 γ𝑧↦𝑦)
  (∘↦-intro _ 𝑤 _ δ𝑥↦𝑤 𝑡𝑤↦y))
    = ∘↦-intro 𝑥 (𝑧 ⊔ᵥ 𝑤) ⟪ y , 𝑦 ⟫ δ𝑥↦𝑧⊔𝑤 ⟨γ,𝑡⟩↦
      where δ𝑥↦𝑧⊔𝑤 = Appmap.↦-↑directed δ δ𝑥↦𝑧 δ𝑥↦𝑤
            γ𝑧⊔𝑤↦𝑦 = appmapLemma₁ {γ = γ} γ𝑧↦𝑦
            𝑡𝑧⊔𝑤↦y = appmapLemma₂ {γ = 𝑡} 𝑡𝑤↦y
            ⟨γ,𝑡⟩↦ = ⟨⟩↦-intro (𝑧 ⊔ᵥ 𝑤) ⟪ y , 𝑦 ⟫
                     γ𝑧⊔𝑤↦𝑦 𝑡𝑧⊔𝑤↦y

compExt : (𝑡 : tAppmap Δ [ 𝐴 ]) → (γ : tAppmap Δ Γ) →
          (δ : tAppmap Γ Δ) →
          (⟨ γ , 𝑡 ⟩ ∘ δ) ≈ ⟨ γ ∘ δ , 𝑡 ∘ δ ⟩
compExt 𝑡 γ δ = ≈-intro (≼-intro compExtLemma₁)
                (≼-intro compExtLemma₂)

<,>-congLemma : 𝑡 ≈ 𝑡′ → γ ≈ γ′ → ∀ 𝑥 𝑦 → ⟨⟩↦ γ 𝑡 𝑥 𝑦 →
                ⟨⟩↦ γ′ 𝑡′ 𝑥 𝑦
<,>-congLemma (≈-intro (≼-intro 𝑡′𝑥↦y) _)
  (≈-intro (≼-intro γ′𝑥↦𝑦) _) 𝑥 ⟪ y , 𝑦 ⟫
  (⟨⟩↦-intro _ _ γ𝑥↦𝑦 𝑡𝑥↦y)
  = ⟨⟩↦-intro 𝑥 ⟪ y , 𝑦 ⟫ (γ′𝑥↦𝑦 𝑥 𝑦 γ𝑥↦𝑦)
    (𝑡′𝑥↦y 𝑥 ⟪ y ⟫ 𝑡𝑥↦y)

<,>-cong : 𝑡 ≈ 𝑡′ → γ ≈ γ′ → ⟨ γ , 𝑡 ⟩ ≈ ⟨ γ′ , 𝑡′ ⟩
<,>-cong 𝑡≈𝑡′ γ≈γ′ = ≈-intro γ𝑡≼γ′𝑡′ γ′𝑡′≼γ𝑡
  where γ𝑡≼γ′𝑡′ = ≼-intro (<,>-congLemma 𝑡≈𝑡′ γ≈γ′)
        𝑡′≈𝑡 = ≈Symmetric 𝑡≈𝑡′
        γ′≈γ = ≈Symmetric γ≈γ′
        γ′𝑡′≼γ𝑡 = ≼-intro (<,>-congLemma 𝑡′≈𝑡 γ′≈γ)

∘-congLemma : γ ≈ δ → γ′ ≈ δ′ → ∀ 𝑥 𝑦 → [ γ ∘ γ′ ] 𝑥 ↦ 𝑦 →
              [ δ ∘ δ′ ] 𝑥 ↦ 𝑦
∘-congLemma (≈-intro (≼-intro 𝑡′𝑧↦𝑦) _)
  (≈-intro (≼-intro γ′𝑥↦𝑧) _) 𝑥 𝑦
  (∘↦-intro _ 𝑧 _ γ𝑥↦𝑧 𝑡𝑧↦𝑦)
  = ∘↦-intro 𝑥 𝑧 𝑦 (γ′𝑥↦𝑧 𝑥 𝑧 γ𝑥↦𝑧) (𝑡′𝑧↦𝑦 𝑧 𝑦 𝑡𝑧↦𝑦)

∘-cong : γ ≈ δ → γ′ ≈ δ′ → (γ ∘ γ′) ≈ (δ ∘ δ′)
∘-cong γ≈δ γ′≈δ′
  = ≈-intro γ∘γ′≼δ∘δ′ δ∘δ′≼γ∘γ′
  where γ∘γ′≼δ∘δ′ = ≼-intro (∘-congLemma γ≈δ γ′≈δ′)
        δ≈γ = ≈Symmetric γ≈δ
        δ′≈γ′ = ≈Symmetric γ′≈δ′
        δ∘δ′≼γ∘γ′ = ≼-intro (∘-congLemma δ≈γ δ′≈γ′)
