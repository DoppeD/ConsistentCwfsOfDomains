{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.Coherence where

open import Base.Core
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun

private
  conElems : ∀ {i} → FinFun {i} → Set
  conElems f = ∀ {u v} → (u , v) ∈ f → con u ⊠ con v

  conPairs : ∀ {i} → FinFun {i} → Set
  conPairs f = ∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → con (u ⊔ u′) → con (v ⊔ v′)

coherence''' : ∀ {i} → {f g h : FinFun {i}} → conElems (f ∪ g) → conElems (f ∪ h) → conElems (g ∪ h) →
              conElems (f ∪ (g ∪ h))
coherence''' {f = f} _ _ _ uv∈ with (∪-lemma₂ {𝑓 = f} uv∈)
coherence''' conElemsfg _ _ _ | inl uv∈f = conElemsfg (∪-lemma₃ uv∈f)
coherence''' {g = g} _ _ conElemsgh _ | inr uv∈g∪h = conElemsgh uv∈g∪h

coherence'' : ∀ {i} → {f g h : FinFun {i}} → conPairs (f ∪ g) → conPairs (f ∪ h) → conPairs (g ∪ h) →
              conPairs (f ∪ (g ∪ h))
coherence'' {f = f} {g} {h} conf∪g conf∪h cong∪h uv∈ u′v′∈ conuu′
  with (∪-lemma₂ {𝑓 = f} uv∈) | ∪-lemma₂ {𝑓 = f} u′v′∈
coherence'' conf∪g _ _ _ _ conuu′ | inl uv∈f | inl u′v′∈f =
  conf∪g (∪-lemma₃ uv∈f) (∪-lemma₃ u′v′∈f) conuu′
coherence'' {g = g} conf∪g conf∪h _ _ _ conuu′ | inl uv∈f | inr u′v′∈g∪h
  with (∪-lemma₂ {𝑓 = g} u′v′∈g∪h)
... | inl u′v′∈g = conf∪g (∪-lemma₃ uv∈f) (∪-lemma₄ u′v′∈g) conuu′
... | inr u′v′∈h = conf∪h (∪-lemma₃ uv∈f) (∪-lemma₄ u′v′∈h) conuu′
coherence'' {g = g} conf∪g conf∪h _ _ _ conuu′ | inr uv∈g∪h | inl u′v′∈f
  with (∪-lemma₂ {𝑓 = g} uv∈g∪h)
... | inl uv∈g = conf∪g (∪-lemma₄ uv∈g) (∪-lemma₃ u′v′∈f) conuu′
... | inr uv∈h = conf∪h (∪-lemma₄ uv∈h) (∪-lemma₃ u′v′∈f) conuu′
coherence'' {g = g} _ _ cong∪h _ _ conuu′ | inr uv∈g∪h | inr u′v′∈g∪h = cong∪h uv∈g∪h u′v′∈g∪h conuu′

coherence' : ∀ {i} → {u v w : Nbh {i}} → con (u ⊔ v) → con (u ⊔ w) → con (v ⊔ w) → con (u ⊔ (v ⊔ w))
coherence' {u = ⊥} _ _ convw = convw
coherence' {u = 0ᵤ} {⊥} _ conuw _ = conuw
coherence' {u = 0ᵤ} {0ᵤ} {⊥} _ _ _ = *
coherence' {u = 0ᵤ} {0ᵤ} {0ᵤ} _ _ _ = *
coherence' {u = s _} {⊥} _ conuw _ = conuw
coherence' {u = s _} {s _} {⊥} conuv _ _ = conuv
coherence' {u = s u} {s _} {s _} = coherence' {u = u}
coherence' {u = ℕ} {⊥} _ conuw _ = conuw
coherence' {u = ℕ} {ℕ} {⊥} _ _ _ = *
coherence' {u = ℕ} {ℕ} {ℕ} _ _ _ = *
coherence' {u = F _} {⊥} _ conuw _ = conuw
coherence' {u = F _} {F _} {⊥} conuv _ _ = conuv
coherence' {u = F f} {F _} {F _} (conPairsfg , conElemsfg) (conPairsfh , conElemsfh) (conPairsgh , conElemsgh)
  = (coherence'' {f = f} conPairsfg conPairsfh conPairsgh) ,
    (coherence''' {f = f} conElemsfg conElemsfh conElemsgh)
coherence' {u = refl _} {⊥} _ conuw _ = conuw
coherence' {u = refl _} {refl _} {⊥} conuv _ _ = conuv
coherence' {u = refl u} {refl _} {refl _} = coherence' {u = u}
coherence' {u = Π _ _} {⊥} _ conuw _ = conuw
coherence' {u = Π _ _} {Π _ _} {⊥} conuv _ _ = conuv
coherence' {u = Π u f} {Π _ _} {Π _ _}
  (conuv , (conPairsfg , conElemsfg)) (conuw , (conPairsfh , conElemsfh)) (convw , (conPairsgh , conElemsgh)) =
  (coherence' {u = u} conuv conuw convw) ,
  ((coherence'' {f = f} conPairsfg conPairsfh conPairsgh) , coherence''' {f = f} conElemsfg conElemsfh conElemsgh)
coherence' {u = 𝒰} {⊥} {w} _ conuw _ = conuw
coherence' {u = 𝒰} {𝒰} {⊥} _ _ _ = *
coherence' {u = 𝒰} {𝒰} {𝒰} _ _ _ = *

coherence : ∀ {i} → {f : FinFun {i}} → conFinFun f → con (pre f) → con (post f)
coherence {f = ∅} _ _ = *
coherence {f = (u , v) ∷ ∅} (_ , conElemsf) _′ with (conElemsf here)
... | (_ , conv) = conAssoc' {u = v} conv
coherence {f = (u , v) ∷ ((u′ , v′) ∷ f′)} (conPairsf , conElemsf) conupref′
  = coherence' {u = v} {v′} {post f′} (conPairsf here (there here) (conLemma₁ {u = u ⊔ u′} (conAssoc₁ {u = u} conupref′)))
    (coherence (subsetIsCon lemma conf) (conTrans {u = u} conupref′))
    (coherence {f = (u′ , v′) ∷ f′} (subsetIsCon ⊆-lemma₃ conf) (conLemma₂ {u = u} conupref′))
  where lemma : ∀ {i} → {u v : Nbh {i} ⊠ Nbh {i}} → ∀ {f} → (u ∷ f) ⊆ (u ∷ (v ∷ f))
        lemma here = here
        lemma (there x∈) = there (there x∈)
        conf : conFinFun ((u , v) ∷ ((u′ , v′) ∷ f′))
        conf = conPairsf , conElemsf
