module Cwf.UniType.Transitivity where

open import Base.Core
open import Cwf.UniType.Coherence
open import Cwf.UniType.Consistency
open import Cwf.UniType.ConsistencyLemmata
open import Cwf.UniType.ConLub
open import Cwf.UniType.Definition
open import Cwf.UniType.FinFun
open import Cwf.UniType.Relation
open import Cwf.UniType.RelationLemmata

open import Agda.Builtin.Equality

Ω : ∀ {f g} → F f ⊑ F g → con (pre f) → ⊑-proof g (pre f) (post f)
Ω {f = ∅} _ _
  = record
      { sub = ∅
      ; preable = *
      ; sub⊆g = ∅-isSubset
      ; pre⊑u = ⊑-bot *
      ; v⊑post = ⊑-bot *
      }
Ω {f = (u , v) ∷ f′} {g} (⊑-F conf cong p) conpref
  with (p here) | Ω {f′} (⊑-F (subsetIsCon ⊆-lemma₃ conf) cong (λ u′v′∈f′ → p (there u′v′∈f′))) (conLemma₂ {u = u} conpref)
... | record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
    | record { sub = rsub ; preable = rpreable ; sub⊆g = rsub⊆g ; pre⊑u = rpre⊑u ; v⊑post = rv⊑post }
  = record
      { sub = sub ∪ rsub
      ; preable = {!!}
      ; sub⊆g = ∪-lemma₁ sub⊆g rsub⊆g
      ; pre⊑u = lemma₁ (a {f = sub} {!!}) (⊑-⊔-lemma₃ pre⊑u rpre⊑u {!!} conpref)
      ; v⊑post = lemma₂ (b {sub} (coherence (subsetIsCon sub⊆g cong) preable)) (⊑-⊔-lemma₃ v⊑post rv⊑post (coherence conf conpref) {!!})
      }
  where lemma₁ : ∀ {u u′ v} → u′ ≡ u → u ⊑ v → u′ ⊑ v
        lemma₁ refl u⊑v = u⊑v
        lemma₂ : ∀ {u v v′} → v′ ≡ v → u ⊑ v → u ⊑ v′
        lemma₂ refl u⊑v = u⊑v
