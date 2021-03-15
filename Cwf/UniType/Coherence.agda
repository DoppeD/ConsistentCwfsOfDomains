module Cwf.UniType.Coherence where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition

private
  conElems : ∀ {i} → FinFun (Nbh {i}) (Nbh {i}) → Set
  conElems f = ∀ {u v} → (u , v) ∈ f → con u ⊠ con v

  conPairs : ∀ {i} → FinFun (Nbh {i}) (Nbh {i}) → Set
  conPairs f = ∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → con (u ⊔ u′) → con (v ⊔ v′)

coherence''' : ∀ {f g h} → conElems (f ∪ g) → conElems (f ∪ h) → conElems (g ∪ h) →
              conElems (f ∪ (g ∪ h))
coherence''' {f} _ _ _ uv∈ with (∪-lemma₂ {𝑓 = f} uv∈)
coherence''' conElemsfg _ _ _ | inl uv∈f = conElemsfg (∪-lemma₃ uv∈f)
coherence''' {g = g} _ _ conElemsgh _ | inr uv∈g∪h = conElemsgh uv∈g∪h

coherence'' : ∀ {f g h} → conPairs (f ∪ g) → conPairs (f ∪ h) → conPairs (g ∪ h) →
              conPairs (f ∪ (g ∪ h))
coherence'' {f} {g} {h} conf∪g conf∪h cong∪h uv∈ u′v′∈ conuu′
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

coherence' : ∀ {u v w} → con (u ⊔ v) → con (u ⊔ w) → con (v ⊔ w) → con (u ⊔ (v ⊔ w))
coherence' {⊥} _ _ convw = convw
coherence' {0ᵤ} {⊥} _ conuw _ = conuw
coherence' {0ᵤ} {0ᵤ} {⊥} _ _ _ = *
coherence' {0ᵤ} {0ᵤ} {0ᵤ} _ _ _ = *
coherence' {s _} {⊥} _ conuw _ = conuw
coherence' {s _} {s _} {⊥} conuv _ _ = conuv
coherence' {s u} {s _} {s _} = coherence' {u}
coherence' {ℕ} {⊥} _ conuw _ = conuw
coherence' {ℕ} {ℕ} {⊥} _ _ _ = *
coherence' {ℕ} {ℕ} {ℕ} _ _ _ = *
coherence' {F _} {⊥} _ conuw _ = conuw
coherence' {F _} {F _} {⊥} conuv _ _ = conuv
coherence' {F f} {F _} {F _} (conPairsfg , conElemsfg) (conPairsfh , conElemsfh) (conPairsgh , conElemsgh)
  = (coherence'' {f} conPairsfg conPairsfh conPairsgh) ,
    (coherence''' {f} conElemsfg conElemsfh conElemsgh)
coherence' {Π _ _} {⊥} _ conuw _ = conuw
coherence' {Π _ _} {Π _ _} {⊥} conuv _ _ = conuv
coherence' {Π u f} {Π _ _} {Π _ _}
  (conuv , (conPairsfg , conElemsfg)) (conuw , (conPairsfh , conElemsfh)) (convw , (conPairsgh , conElemsgh)) =
  (coherence' {u = u} conuv conuw convw) ,
  ((coherence'' {f} conPairsfg conPairsfh conPairsgh) , coherence''' {f} conElemsfg conElemsfh conElemsgh)
coherence' {𝒰} {⊥} {w} _ conuw _ = conuw
coherence' {𝒰} {𝒰} {⊥} _ _ _ = *
coherence' {𝒰} {𝒰} {𝒰} _ _ _ = *

coherence : ∀ {f} → conFinFun f → con (pre f) → con (post f)
coherence {∅} _ _ = *
coherence {(u , v) ∷ ∅} (_ , conElemsf) _′ with (conElemsf here)
... | (_ , conv) = conAssoc' {u = v} conv
coherence {(u , v) ∷ ((u′ , v′) ∷ f′)} (conPairsf , conElemsf) conupref′
  = coherence' {v} {v′} {post f′} (conPairsf here (there here) (conLemma₁ {u ⊔ u′} (conAssoc {u} conupref′)))
    (coherence (subsetIsCon lemma conf) (conTrans {u} conupref′))
    (coherence {f = (u′ , v′) ∷ f′} (subsetIsCon ⊆-lemma₃ conf) (conLemma₂ {u} conupref′))
  where lemma : ∀ {u v f} → (u ∷ f) ⊆ (u ∷ (v ∷ f))
        lemma here = here
        lemma (there x∈) = there (there x∈)
        conf : conFinFun ((u , v) ∷ ((u′ , v′) ∷ f′))
        conf = conPairsf , conElemsf
