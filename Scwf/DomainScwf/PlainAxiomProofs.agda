{-# OPTIONS --safe #-}

module Scwf.DomainScwf.PlainAxiomProofs where

open import Appmap.Equivalence
open import Appmap.Lemmata
open import Appmap.Composition.Instance
open import Appmap.Composition.Relation
open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Empty.Instance
open import Scwf.DomainScwf.Appmap.Empty.Relation
open import Scwf.DomainScwf.Appmap.Identity.Instance
open import Scwf.DomainScwf.Appmap.Identity.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.Comprehension.p.Instance
open import Scwf.DomainScwf.Comprehension.p.Relation
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Relation
open import Scwf.DomainScwf.Comprehension.q.Instance
open import Scwf.DomainScwf.Comprehension.q.Relation

private
  variable
    γ γ′ : Sub Γ Δ
    δ δ′ : Sub Δ Θ
    θ : Sub Θ Λ
    𝑡 𝑡′ : Term Δ 𝐴

subAssocLemma₁ : ∀ {𝑥 𝑦} → [ (θ ∘ δ) ∘ γ ] 𝑥 ↦ 𝑦 →
                 [ θ ∘ (δ ∘ γ) ] 𝑥 ↦ 𝑦
subAssocLemma₁ (∘↦-intro γ𝑥↦𝑧 (∘↦-intro δ𝑧↦𝑤 θ𝑤↦𝑦))
  = ∘↦-intro (∘↦-intro γ𝑥↦𝑧 δ𝑧↦𝑤) θ𝑤↦𝑦

subAssocLemma₂ : ∀ {𝑥 𝑦} → [ θ ∘ (δ ∘ γ) ] 𝑥 ↦ 𝑦 →
                 [ (θ ∘ δ) ∘ γ ] 𝑥 ↦ 𝑦
subAssocLemma₂ (∘↦-intro (∘↦-intro γ𝑥↦𝑤 δ𝑤↦𝑧) θ𝑧↦𝑦)
  = ∘↦-intro γ𝑥↦𝑤 (∘↦-intro δ𝑤↦𝑧 θ𝑧↦𝑦)

subAssoc : (γ : Sub Γ Δ) → (δ : Sub Δ Θ) →
           (θ : Sub Θ Λ) →
           ((θ ∘ δ) ∘ γ) ≈ (θ ∘ (δ ∘ γ))
subAssoc γ δ θ = ≈-intro (≼-intro subAssocLemma₁)
              (≼-intro subAssocLemma₂)

pConsLemma₁ : ∀ {𝑥 𝑦} → [ p Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦 →
              [ γ ] 𝑥 ↦ 𝑦
pConsLemma₁ {γ = γ} (∘↦-intro (⟨⟩↦-intro γ𝑥↦𝑧 _) (p↦-intro 𝑦⊑𝑧))
  = Appmap.↦-↓closed γ 𝑦⊑𝑧 γ𝑥↦𝑧

pConsLemma₂ : ∀ {𝑥 𝑦} → [ γ ] 𝑥 ↦ 𝑦 →
              [ p Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ 𝑦
pConsLemma₂ {γ = γ} {𝐴 = 𝐴} {𝑡} γ𝑥↦𝑦
  = ∘↦-intro γ𝑡𝑥↦⊥𝑦 p⊥𝑦↦𝑦
  where 𝑡𝑥↦⊥ = Appmap.↦-bottom 𝑡
        γ𝑡𝑥↦⊥𝑦 = ⟨⟩↦-intro {𝑦 = ⟪ NbhSys.⊥ 𝐴 ,, _ ⟫} γ𝑥↦𝑦 𝑡𝑥↦⊥
        p⊥𝑦↦𝑦 = p↦-intro (NbhSys.⊑-refl (ValNbhSys _))

pCons : (γ : Sub Δ Γ) → (𝑡 : Term Δ 𝐴) →
        (p Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩) ≈ γ
pCons γ 𝑡 = ≈-intro (≼-intro pConsLemma₁)
            (≼-intro pConsLemma₂)

qConsLemma₁ : ∀ {𝑥 y} → [ q Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ y →
              [ 𝑡 ] 𝑥 ↦ y
qConsLemma₁ {𝐴 = 𝐴} {𝑡 = 𝑡} {y = y}
  (∘↦-intro (⟨⟩↦-intro _ 𝑡𝑥↦z) (q↦-intro y⊑z))
  = Appmap.↦-↓closed 𝑡 y⊑z 𝑡𝑥↦z

qConsLemma₂ : ∀ {𝑥 y} → [ 𝑡 ] 𝑥 ↦ y →
              [ q Γ 𝐴 ∘ ⟨ γ , 𝑡 ⟩ ] 𝑥 ↦ y
qConsLemma₂ {𝐴 = 𝐴} {γ = γ} {y = y} 𝑡𝑥↦y =
  ∘↦-intro γ𝑡𝑥↦y⊥ qy⊥↦y
  where γ𝑥↦⊥ = Appmap.↦-bottom γ
        qy⊥↦y = q↦-intro (NbhSys.⊑-refl 𝐴)
        γ𝑡𝑥↦y⊥ = ⟨⟩↦-intro {𝑦 = ⟪ y ,, ⊥ᵥ ⟫} γ𝑥↦⊥ 𝑡𝑥↦y

qCons : (γ : Sub Δ Γ) → (𝑡 : Term Δ 𝐴) →
        ((q Γ 𝐴) ∘ ⟨ γ , 𝑡 ⟩) ≈ 𝑡
qCons γ 𝑡 = ≈-intro (≼-intro qConsLemma₁)
            (≼-intro qConsLemma₂)

idExtLemma₁ : ∀ {𝑥 𝑦} → 𝑥 id↦ 𝑦 → ⟨⟩↦ (p Γ 𝐴) (q Γ 𝐴) 𝑥 𝑦
idExtLemma₁ (id↦-intro (⊑ᵥ-cons _ y⊑x 𝑦⊑𝑥))
  = ⟨⟩↦-intro px𝑥↦𝑦 qx𝑥↦𝑦
  where px𝑥↦𝑦 = p↦-intro 𝑦⊑𝑥
        qx𝑥↦𝑦 = q↦-intro y⊑x

idExtLemma₂ : ∀ {𝑥 𝑦} → ⟨⟩↦ (p Γ 𝐴) (q Γ 𝐴) 𝑥 𝑦 →
              𝑥 id↦ 𝑦
idExtLemma₂ {Γ = Γ} {𝐴 = 𝐴}
  (⟨⟩↦-intro (p↦-intro 𝑦⊑𝑥) (q↦-intro y⊑x))
  = id↦-intro y𝑦⊑x𝑥
  where y𝑦⊑x𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) y⊑x 𝑦⊑𝑥

idExt : idMap (𝐴 :: Γ) ≈ ⟨ p Γ 𝐴 , q Γ 𝐴 ⟩
idExt = ≈-intro (≼-intro idExtLemma₁)
        (≼-intro idExtLemma₂)

idLLemma₁ : ∀ {𝑥 𝑦} → [ idMap Γ ∘ γ ] 𝑥 ↦ 𝑦 →
            [ γ ] 𝑥 ↦ 𝑦
idLLemma₁ {γ = γ} (∘↦-intro γ𝑥↦𝑧 (id↦-intro 𝑦⊑𝑧))
  = Appmap.↦-↓closed γ 𝑦⊑𝑧 γ𝑥↦𝑧

idLLemma₂ : ∀ {𝑥 𝑦} → [ γ ] 𝑥 ↦ 𝑦 →
            [ idMap Γ ∘ γ ] 𝑥 ↦ 𝑦
idLLemma₂ 𝑥↦𝑦 = ∘↦-intro 𝑥↦𝑦 (id↦-intro 𝑦⊑𝑦)
   where 𝑦⊑𝑦 = NbhSys.⊑-refl (ValNbhSys _)

idL : (γ : Sub Δ Γ) → (idMap Γ ∘ γ) ≈ γ
idL γ = ≈-intro (≼-intro idLLemma₁) (≼-intro idLLemma₂)

idRLemma₁ : ∀ {𝑥 𝑦} → [ γ ∘ idMap Δ ] 𝑥 ↦ 𝑦 →
            [ γ ] 𝑥 ↦ 𝑦
idRLemma₁ {γ = γ} (∘↦-intro (id↦-intro 𝑧⊑𝑥) γ𝑧↦𝑦)
  = Appmap.↦-mono γ 𝑧⊑𝑥 γ𝑧↦𝑦

idRLemma₂ : ∀ {𝑥 𝑦} → [ γ ] 𝑥 ↦ 𝑦 →
            [ γ ∘ idMap Δ ] 𝑥 ↦ 𝑦
idRLemma₂ 𝑥↦𝑦
  = ∘↦-intro (id↦-intro 𝑥⊑𝑥) 𝑥↦𝑦
  where 𝑥⊑𝑥 = NbhSys.⊑-refl (ValNbhSys _)

idR : (γ : Sub Δ Γ) → (γ ∘ idMap Δ) ≈ γ
idR γ = ≈-intro (≼-intro idRLemma₁) (≼-intro idRLemma₂)

id₀Lemma₁ : ∀ {𝑥 𝑦} → 𝑥 id↦ 𝑦 → 𝑥 empty↦ 𝑦
id₀Lemma₁ {⟪⟫} {⟪⟫} id𝑥↦𝑦 = empty↦-intro

id₀Lemma₂ : ∀ {𝑥 𝑦} → 𝑥 empty↦ 𝑦 → 𝑥 id↦ 𝑦
id₀Lemma₂ {⟪⟫} {⟪⟫} em𝑥↦𝑦 = id↦-intro ⊑ᵥ-nil

id₀ : idMap [] ≈ emptyMap
id₀ = ≈-intro (≼-intro id₀Lemma₁) (≼-intro id₀Lemma₂)

<>-zeroLemma₁ : ∀ {𝑥 𝑦} → [ emptyMap ∘ γ ] 𝑥 ↦ 𝑦 →
                𝑥 empty↦ 𝑦
<>-zeroLemma₁ {𝑦 = ⟪⟫} _ = empty↦-intro

<>-zeroLemma₂ : ∀ {𝑥 𝑦} → 𝑥 empty↦ 𝑦 →
                [ emptyMap ∘ γ ] 𝑥 ↦ 𝑦
<>-zeroLemma₂ {γ = γ} {𝑦 = ⟪⟫} empty↦-intro
  = ∘↦-intro γ𝑥↦⊥ empty↦-intro
    where γ𝑥↦⊥ = Appmap.↦-bottom γ

<>-zero : (γ : Sub Γ Δ) → (emptyMap ∘ γ) ≈ emptyMap
<>-zero γ = ≈-intro (≼-intro <>-zeroLemma₁)
            (≼-intro <>-zeroLemma₂)

idSubLemma₁ : ∀ {𝑥 𝑦} → [ 𝑡 ∘ idMap Γ ] 𝑥 ↦ 𝑦 →
              [ 𝑡 ] 𝑥 ↦ 𝑦
idSubLemma₁ {𝑡 = 𝑡} (∘↦-intro (id↦-intro 𝑧⊑𝑥) 𝑡𝑧↦𝑦)
  = Appmap.↦-mono 𝑡 𝑧⊑𝑥 𝑡𝑧↦𝑦

idSubLemma₂ : ∀ {𝑥 𝑦} → [ 𝑡 ] 𝑥 ↦ 𝑦 →
              [ 𝑡 ∘ idMap Γ ] 𝑥 ↦ 𝑦
idSubLemma₂ {𝑡 = 𝑡} 𝑡𝑥↦𝑦
  = ∘↦-intro (id↦-intro 𝑥⊑𝑥) 𝑡𝑥↦𝑦
  where 𝑥⊑𝑥 = NbhSys.⊑-refl (ValNbhSys _)

idSub : (𝑡 : Term Γ 𝐴) →
        (𝑡 ∘ idMap Γ) ≈ 𝑡
idSub t = ≈-intro (≼-intro idSubLemma₁)
          (≼-intro idSubLemma₂)

compSubLemma₁ : ∀ {𝑥 𝑦} → [ 𝑡 ∘ (γ ∘ δ) ] 𝑥 ↦ 𝑦 →
                [ (𝑡 ∘ γ) ∘ δ ] 𝑥 ↦ 𝑦
compSubLemma₁ (∘↦-intro (∘↦-intro δ𝑥↦𝑤 γ𝑤↦𝑧) 𝑡𝑧↦𝑦)
  = ∘↦-intro δ𝑥↦𝑤 (∘↦-intro γ𝑤↦𝑧 𝑡𝑧↦𝑦)

compSubLemma₂ : ∀ {𝑥 𝑦} → [ (𝑡 ∘ γ) ∘ δ ] 𝑥 ↦ 𝑦 →
                [ 𝑡 ∘ (γ ∘ δ) ] 𝑥 ↦ 𝑦
compSubLemma₂ (∘↦-intro δ𝑥↦𝑧 (∘↦-intro γ𝑧↦𝑤 𝑡𝑤↦𝑦))
  = ∘↦-intro (∘↦-intro δ𝑥↦𝑧 γ𝑧↦𝑤) 𝑡𝑤↦𝑦

compSub : (𝑡 : Term Δ 𝐴) → (γ : Sub Γ Δ) →
          (δ : Sub Θ Γ) →
          (𝑡 ∘ (γ ∘ δ)) ≈ ((𝑡 ∘ γ) ∘ δ)
compSub 𝑡 γ δ = ≈-intro (≼-intro compSubLemma₁)
                (≼-intro compSubLemma₂)

compExtLemma₁ : ∀ {𝑥 𝑦} → [ ⟨ γ , 𝑡 ⟩ ∘ δ ] 𝑥 ↦ 𝑦 →
                [ ⟨ γ ∘ δ , 𝑡 ∘ δ ⟩ ] 𝑥 ↦ 𝑦
compExtLemma₁ (∘↦-intro δ𝑥↦𝑧 (⟨⟩↦-intro γ𝑧↦𝑦 𝑡𝑧↦y))
  = ⟨⟩↦-intro (∘↦-intro δ𝑥↦𝑧 γ𝑧↦𝑦) (∘↦-intro δ𝑥↦𝑧 𝑡𝑧↦y)

compExtLemma₂ : ∀ {𝑥 𝑦} → [ ⟨ γ ∘ δ , 𝑡 ∘ δ ⟩ ] 𝑥 ↦ 𝑦 →
                [ ⟨ γ , 𝑡 ⟩ ∘ δ ] 𝑥 ↦ 𝑦
compExtLemma₂ {γ = γ} {δ = δ} {𝑡 = 𝑡}
  (⟨⟩↦-intro (∘↦-intro δ𝑥↦𝑧 γ𝑧↦𝑦) (∘↦-intro δ𝑥↦𝑤 𝑡𝑤↦y))
    = ∘↦-intro δ𝑥↦𝑧⊔𝑤 ⟨γ,𝑡⟩↦
      where con𝑧𝑤 = Appmap.↦-con δ δ𝑥↦𝑧 δ𝑥↦𝑤 valConRefl
            δ𝑥↦𝑧⊔𝑤 = Appmap.↦-↑directed δ δ𝑥↦𝑧 δ𝑥↦𝑤 con𝑧𝑤
            γ𝑧⊔𝑤↦𝑦 = appmapLemma₁ {γ = γ} con𝑧𝑤 γ𝑧↦𝑦
            𝑡𝑧⊔𝑤↦y = appmapLemma₂ {γ = 𝑡} con𝑧𝑤 𝑡𝑤↦y
            ⟨γ,𝑡⟩↦ = ⟨⟩↦-intro γ𝑧⊔𝑤↦𝑦 𝑡𝑧⊔𝑤↦y

compExt : (𝑡 : Term Δ 𝐴) → (γ : Sub Δ Γ) →
          (δ : Sub Γ Δ) →
          (⟨ γ , 𝑡 ⟩ ∘ δ) ≈ ⟨ γ ∘ δ , 𝑡 ∘ δ ⟩
compExt 𝑡 γ δ = ≈-intro (≼-intro compExtLemma₁)
                (≼-intro compExtLemma₂)

<,>-congLemma : 𝑡 ≈ 𝑡′ → γ ≈ γ′ → ∀ {𝑥 𝑦} → ⟨⟩↦ γ 𝑡 𝑥 𝑦 →
                ⟨⟩↦ γ′ 𝑡′ 𝑥 𝑦
<,>-congLemma (≈-intro (≼-intro 𝑡′𝑥↦y) _)
  (≈-intro (≼-intro γ′𝑥↦𝑦) _) (⟨⟩↦-intro γ𝑥↦𝑦 𝑡𝑥↦y)
  = ⟨⟩↦-intro (γ′𝑥↦𝑦 γ𝑥↦𝑦) (𝑡′𝑥↦y 𝑡𝑥↦y)

<,>-cong : 𝑡 ≈ 𝑡′ → γ ≈ γ′ → ⟨ γ , 𝑡 ⟩ ≈ ⟨ γ′ , 𝑡′ ⟩
<,>-cong 𝑡≈𝑡′ γ≈γ′ = ≈-intro γ𝑡≼γ′𝑡′ γ′𝑡′≼γ𝑡
  where γ𝑡≼γ′𝑡′ = ≼-intro (<,>-congLemma 𝑡≈𝑡′ γ≈γ′)
        𝑡′≈𝑡 = ≈Symmetric 𝑡≈𝑡′
        γ′≈γ = ≈Symmetric γ≈γ′
        γ′𝑡′≼γ𝑡 = ≼-intro (<,>-congLemma 𝑡′≈𝑡 γ′≈γ)

∘-congLemma : {π η : Appmap 𝐵 𝐶} → {π′ η′ : Appmap 𝐴 𝐵} →
              π ≈ η → π′ ≈ η′ → ∀ {x y} → [ π ∘ π′ ] x ↦ y →
              [ η ∘ η′ ] x ↦ y
∘-congLemma (≈-intro (≼-intro ηx↦y) _)
  (≈-intro (≼-intro η′x↦y) _) (∘↦-intro η′x↦z ηz↦y)
  = ∘↦-intro (η′x↦y η′x↦z) (ηx↦y ηz↦y)

∘-cong : {π η : Appmap 𝐵 𝐶} → {π′ η′ : Appmap 𝐴 𝐵} →
         π ≈ η → π′ ≈ η′ → (π ∘ π′) ≈ (η ∘ η′)
∘-cong π≈η π′≈η′
  = ≈-intro π∘π′≼η∘η′ η∘η′≼π∘π′
  where π∘π′≼η∘η′ = ≼-intro (∘-congLemma π≈η π′≈η′)
        η≈π = ≈Symmetric π≈η
        η′≈π′ = ≈Symmetric π′≈η′
        η∘η′≼π∘π′ = ≼-intro (∘-congLemma η≈π η′≈π′)
