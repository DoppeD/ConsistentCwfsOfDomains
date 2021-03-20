{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.Transitivity where

open import Base.Core
open import Cwf.DomainCwf.UniType.Coherence
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.RelationLemmata

open import Agda.Builtin.Equality

Ω : ∀ {i} → {f g : FinFun {i}} → F f ⊑ F g → con (pre f) → ⊑-proof g (pre f) (post f)
Ω {f = ∅} _ _
  = record
      { sub = ∅
      ; preable = *
      ; sub⊆g = ∅-isSubset
      ; pre⊑u = ⊑-bot *
      ; v⊑post = ⊑-bot *
      }
Ω {f = (u , v) ∷ f′} {g} (⊑-F conf cong p) conpref
  with (p here) | Ω {f = f′} (⊑-F (subsetIsCon ⊆-lemma₃ conf) cong (λ u′v′∈f′ → p (there u′v′∈f′))) (conLemma₂ {u = u} conpref)
... | record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
    | record { sub = rsub ; preable = rpreable ; sub⊆g = rsub⊆g ; pre⊑u = rpre⊑u ; v⊑post = rv⊑post }
  = record
      { sub = sub ∪ rsub
      ; preable = conpre∪
      ; sub⊆g = ∪-lemma₁ sub⊆g rsub⊆g
      ; pre⊑u = lemma₁ (preUnionLemma' {f = sub} conpresubs) (⊑-⊔-lemma₃ pre⊑u rpre⊑u conpresubs conpref)
      ; v⊑post = lemma₂ (postUnionLemma' {f = sub} conpostsub conpost∪) (⊑-⊔-lemma₃ v⊑post rv⊑post (coherence conf conpref) conpostsubs)
      }
  where lemma₁ : ∀ {u u′ v} → u′ ≡ u → u ⊑ v → u′ ⊑ v
        lemma₁ refl u⊑v = u⊑v
        lemma₂ : ∀ {u v v′} → v ≡ v′ → u ⊑ v → u ⊑ v′
        lemma₂ refl u⊑v = u⊑v
        conpresubs = (Con-⊔ (⊑-⊔-lemma₁ pre⊑u conpref) (⊑-⊔-lemma₂ rpre⊑u conpref))
        conpre∪ = preUnionLemma {f = sub} conpresubs
        conpostsub = coherence {f = sub} (subsetIsCon sub⊆g cong) preable
        conpost∪ = coherence {f = sub ∪ rsub} (subsetIsCon (∪-lemma₁ sub⊆g rsub⊆g) cong) conpre∪
        conpostsubs = postUnionLemma {f = sub} conpostsub conpost∪

⊑-trans : ∀ {i} → {u v w : Nbh {i}} → u ⊑ v → v ⊑ w → u ⊑ w
⊑-trans' : ∀ {i} → {f g h : FinFun {i}} → ∀ {u v} → (u , v) ∈ f → ⊑-proof g u v → (F g) ⊑ (F h) → ⊑-proof h u v

⊑-trans (⊑-bot _) v⊑w = ⊑-bot (⊠-snd (orderOnlyCon v⊑w))
⊑-trans ⊑-0 v⊑w = v⊑w
⊑-trans (⊑-s u⊑v) (⊑-s v⊑w) = ⊑-s (⊑-trans u⊑v v⊑w)
⊑-trans ⊑-ℕ v⊑w = v⊑w
⊑-trans (⊑-F conf cong p₁) (⊑-F _ conh p₂)
  = ⊑-F conf conh (λ uv∈f → ⊑-trans' uv∈f (p₁ uv∈f) (⊑-F cong conh p₂))
⊑-trans (⊑-Π u⊑v f⊑g) (⊑-Π v⊑w g⊑h) = ⊑-Π (⊑-trans u⊑v v⊑w) (⊑-trans f⊑g g⊑h)
⊑-trans ⊑-𝒰 v⊑w = v⊑w

⊑-trans' {h = h} here
  record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  (⊑-F cong conh p) with (Ω (⊑-F (subsetIsCon sub⊆g cong) conh (shrink-⊑ sub⊆g (⊑-F cong conh p))) preable)
... | record { sub = sub′ ; preable = preable′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
  = record
      { sub = sub′
      ; preable = preable′
      ; sub⊆g = sub⊆g′
      ; pre⊑u = ⊑-trans pre⊑u′ pre⊑u
      ; v⊑post = ⊑-trans v⊑post v⊑post′
      }
⊑-trans' (there uv∈f′) proofguv g⊑h = ⊑-trans' uv∈f′ proofguv g⊑h
