{-# OPTIONS --safe #-}

open import Base.Core hiding (<_,_>)

module Scwf.DomainScwf.ProductStructure.AxiomProofs (𝐴 𝐵 : Ty) where

open import Appmap.Equivalence
open import Base.Variables hiding (𝐴 ; 𝐵)
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ProductStructure.fst.Instance
open import Scwf.DomainScwf.ProductStructure.fst.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
  renaming (<_,_> to ⟨_,_⟩)
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance
open import Scwf.DomainScwf.ProductStructure.Pair.Instance
open import Scwf.DomainScwf.ProductStructure.Pair.Relation
open import Scwf.DomainScwf.ProductStructure.snd.Instance
open import Scwf.DomainScwf.ProductStructure.snd.Relation
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Instance

private
  variable
    𝑡 𝑡′ : tAppmap Γ [ 𝐴 ]
    𝑢 𝑢′ : tAppmap Γ [ 𝐵 ]
    𝑣 𝑣′ : tAppmap Γ [ 𝐴 × 𝐵 ]

fstAxiomLemma₁ : ∀ {𝑥 𝑦} → [ fst < 𝑡 , 𝑢 > ] 𝑥 ↦ 𝑦 →
                 [ 𝑡 ] 𝑥 ↦ 𝑦
fstAxiomLemma₁ {𝑡 = 𝑡} (fst-intro₁ y⊑⊥)
  = Appmap.↦-↓closed 𝑡 tup-y⊑⊥ (Appmap.↦-bottom 𝑡)
  where tup-y⊑⊥ = ⊑ᵥ-cons [ 𝐴 ] y⊑⊥ ⊑ᵥ-nil
fstAxiomLemma₁ (fst-intro₂ (<>↦-intro₂ 𝑡𝑥↦y₁ _))
  = 𝑡𝑥↦y₁

fstAxiomLemma₂ : ∀ {𝑥 𝑦} → [ 𝑡 ] 𝑥 ↦ 𝑦 →
                 [ fst < 𝑡 , 𝑢 > ] 𝑥 ↦ 𝑦
fstAxiomLemma₂ {𝑢 = 𝑢} {𝑦 = ⟪ y₁ , ⟪⟫ ⟫} 𝑡𝑥↦y₁
  = fst-intro₂ ⟨⟩𝑥↦y₁⊥
  where 𝑢𝑥↦⊥ = Appmap.↦-bottom 𝑢
        ⟨⟩𝑥↦y₁⊥ = <>↦-intro₂ 𝑡𝑥↦y₁ 𝑢𝑥↦⊥

fstAxiom : fst < 𝑡 , 𝑢 > ≈ 𝑡
fstAxiom = ≈-intro (≼-intro fstAxiomLemma₁)
            (≼-intro fstAxiomLemma₂)

sndAxiomLemma₁ : ∀ {𝑥 𝑦} → [ snd < 𝑡 , 𝑢 > ] 𝑥 ↦ 𝑦 →
                 [ 𝑢 ] 𝑥 ↦ 𝑦
sndAxiomLemma₁ {𝑢 = 𝑢} (snd-intro₁ y⊑⊥)
  = Appmap.↦-↓closed 𝑢 tup-y⊑⊥ (Appmap.↦-bottom 𝑢)
  where tup-y⊑⊥ = ⊑ᵥ-cons [ 𝐵 ] y⊑⊥ ⊑ᵥ-nil
sndAxiomLemma₁ (snd-intro₂ (<>↦-intro₂ _ 𝑢𝑥↦y₂))
  = 𝑢𝑥↦y₂

sndAxiomLemma₂ : ∀ {𝑥 𝑦} → [ 𝑢 ] 𝑥 ↦ 𝑦 →
                 [ snd < 𝑡 , 𝑢 > ] 𝑥 ↦ 𝑦
sndAxiomLemma₂ {𝑡 = 𝑡} {𝑦 = ⟪ y₁ , ⟪⟫ ⟫} 𝑡𝑥↦y₁
  = snd-intro₂ ⟨⟩𝑥↦⊥y₁
  where 𝑡𝑥↦⊥ = Appmap.↦-bottom 𝑡
        ⟨⟩𝑥↦⊥y₁ = <>↦-intro₂ 𝑡𝑥↦⊥ 𝑡𝑥↦y₁

sndAxiom : snd < 𝑡 , 𝑢 > ≈ 𝑢
sndAxiom = ≈-intro (≼-intro sndAxiomLemma₁)
            (≼-intro sndAxiomLemma₂)

pairSubLemma₁ : {γ : tAppmap Δ Γ} → ∀ {𝑥 𝑦} →
                [ < 𝑡 , 𝑢 > ∘ γ ] 𝑥 ↦ 𝑦 →
                [ < 𝑡 ∘ γ , 𝑢 ∘ γ > ] 𝑥 ↦ 𝑦
pairSubLemma₁ (∘↦-intro _ <>↦-intro₁)
  = <>↦-intro₁
pairSubLemma₁ (∘↦-intro 𝑡𝑥↦𝑧 (<>↦-intro₂ 𝑡𝑧↦y₁ 𝑢𝑧↦y₂))
  = <>↦-intro₂ (∘↦-intro 𝑡𝑥↦𝑧 𝑡𝑧↦y₁) (∘↦-intro 𝑡𝑥↦𝑧 𝑢𝑧↦y₂)

pairSubLemma₂ : {γ : tAppmap Δ Γ} → ∀ {𝑥 𝑦} →
                [ < 𝑡 ∘ γ , 𝑢 ∘ γ > ] 𝑥 ↦ 𝑦 →
                [ < 𝑡 , 𝑢 > ∘ γ ] 𝑥 ↦ 𝑦
pairSubLemma₂ {γ = γ} <>↦-intro₁
  = ∘↦-intro (Appmap.↦-bottom γ) <>↦-intro₁
pairSubLemma₂ {𝑡 = 𝑡} {𝑢 = 𝑢} {γ}
  (<>↦-intro₂ (∘↦-intro γ𝑥↦𝑧 𝑡𝑧↦y₁) (∘↦-intro γ𝑥↦𝑤 𝑢𝑤↦y₂))
  = ∘↦-intro γ𝑥↦𝑧⊔𝑤 𝑧𝑤↦y₁y₂
  where con𝑧𝑤 = Appmap.↦-con γ γ𝑥↦𝑧 γ𝑥↦𝑤 valConRefl
        γ𝑥↦𝑧⊔𝑤 = Appmap.↦-↑directed γ γ𝑥↦𝑧 γ𝑥↦𝑤 con𝑧𝑤
        z⊑z⊔w = NbhSys.⊑-⊔-fst (ValNbhSys _) con𝑧𝑤
        𝑡𝑧⊔𝑤↦y₁ = Appmap.↦-mono 𝑡 z⊑z⊔w 𝑡𝑧↦y₁
        w⊑z⊔w = NbhSys.⊑-⊔-snd (ValNbhSys _) con𝑧𝑤
        𝑢𝑧⊔𝑤↦y₂ = Appmap.↦-mono 𝑢 w⊑z⊔w 𝑢𝑤↦y₂
        𝑧𝑤↦y₁y₂ = <>↦-intro₂ 𝑡𝑧⊔𝑤↦y₁ 𝑢𝑧⊔𝑤↦y₂

pairSub : {γ : tAppmap Δ Γ} →
          (< 𝑡 , 𝑢 > ∘ γ) ≈ < (𝑡 ∘ γ) , (𝑢 ∘ γ) >
pairSub = ≈-intro (≼-intro pairSubLemma₁)
              (≼-intro pairSubLemma₂)

fstCongLemma₁ : 𝑣 ≈ 𝑣′ → ∀ {𝑥 𝑦} → [ fst 𝑣 ] 𝑥 ↦ 𝑦 →
                [ fst 𝑣′ ] 𝑥 ↦ 𝑦
fstCongLemma₁ _ (fst-intro₁ y⊑⊥)
  = fst-intro₁ y⊑⊥
fstCongLemma₁ (≈-intro (≼-intro p) _) (fst-intro₂ 𝑣𝑥↦y₁y₂)
  = fst-intro₂ (p 𝑣𝑥↦y₁y₂)

fstCong : 𝑣 ≈ 𝑣′ →  fst 𝑣 ≈ fst 𝑣′
fstCong 𝑣≈𝑣′
  = ≈-intro (≼-intro (fstCongLemma₁ 𝑣≈𝑣′)) fst′≼fst
  where fst′≼fst = ≼-intro (fstCongLemma₁ (≈Symmetric 𝑣≈𝑣′))

sndCongLemma₁ : 𝑣 ≈ 𝑣′ → ∀ {𝑥 𝑦} → [ snd 𝑣 ] 𝑥 ↦ 𝑦 →
                [ snd 𝑣′ ] 𝑥 ↦ 𝑦
sndCongLemma₁ _ (snd-intro₁ y⊑⊥)
  = snd-intro₁ y⊑⊥
sndCongLemma₁ (≈-intro (≼-intro p) _) (snd-intro₂ 𝑣𝑥↦y₁y₂)
  = snd-intro₂ (p 𝑣𝑥↦y₁y₂)

sndCong : 𝑣 ≈ 𝑣′ → snd 𝑣 ≈ snd 𝑣′
sndCong 𝑣≈𝑣′
  = ≈-intro (≼-intro (sndCongLemma₁ 𝑣≈𝑣′)) snd′≼snd
  where snd′≼snd = ≼-intro (sndCongLemma₁ (≈Symmetric 𝑣≈𝑣′))

pairCongLemma₁ : 𝑡 ≈ 𝑡′ → 𝑢 ≈ 𝑢′ →
                 {𝑥 : Valuation Γ} → ∀ {𝑦} →
                 [ < 𝑡 , 𝑢 > ] 𝑥 ↦ 𝑦 →
                 [ < 𝑡′ , 𝑢′ > ] 𝑥 ↦ 𝑦
pairCongLemma₁ _ _ <>↦-intro₁ = <>↦-intro₁
pairCongLemma₁ (≈-intro (≼-intro p₁) _)
  (≈-intro (≼-intro p₂) _) (<>↦-intro₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂)
  = <>↦-intro₂ (p₁ 𝑡𝑥↦y₁) (p₂ 𝑢𝑥↦y₂)

pairCong : 𝑡 ≈ 𝑡′ → 𝑢 ≈ 𝑢′ → < 𝑡 , 𝑢 > ≈ < 𝑡′ , 𝑢′ >
pairCong 𝑡≈𝑡′ 𝑢≈𝑢′
  = ≈-intro (≼-intro (pairCongLemma₁ 𝑡≈𝑡′ 𝑢≈𝑢′)) pair′≼pair
  where pair′≼pair = ≼-intro (pairCongLemma₁
                     (≈Symmetric 𝑡≈𝑡′) (≈Symmetric 𝑢≈𝑢′))
