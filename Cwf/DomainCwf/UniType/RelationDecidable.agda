{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.RelationDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.AxiomProofs
open import Cwf.DomainCwf.UniType.Coherence
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyDecidable
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.RelationLemmata

open import Agda.Builtin.Size

record Largest {i : Size} (f : FinFun {i}) (w : Nbh {i}) : Set where
  field
    sub : FinFun {i}
    sub⊆f : sub ⊆ f
    pre⊑w : pre sub ⊑ w
    allSmalleru : {u v : Nbh {i}} → (u , v) ∈ f → u ⊑ w → (u , v) ∈ sub

largest : ∀ {i} → (f : FinFun {i}) → (w : Nbh {i}) → con w →
          (∀ {u v} → (u , v) ∈ f → Decidable (u ⊑ w)) →
          Largest f w
largest {i} ∅ w conw _ =
  record
    { sub = ∅
    ; sub⊆f = ∅-isSubset
    ; pre⊑w = ⊑-bot conw
    ; allSmalleru = xy∈∅-abs
    }
largest ((u , v) ∷ f′) w conw p
  with (p here) | largest f′ w conw λ u′v′∈f′ → p (there u′v′∈f′)
... | inl u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru }
  = record
      { sub = (u , v) ∷ sub
      ; sub⊆f = ⊆-lemma₄ here (λ u′v′∈sub → there (sub⊆f u′v′∈sub))
      ; pre⊑w = ⊑-⊔ u⊑w pre⊑w (Con-⊔ u⊑w pre⊑w)
      ; allSmalleru = lemma
      }
      where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → u′ ⊑ w → (u′ , v′) ∈ ((u , v) ∷ sub)
            lemma here _ = here
            lemma (there u′v′∈f′) u′⊑w = there (allSmalleru u′v′∈f′ u′⊑w)
... | inr ¬u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru }
  = record
      { sub = sub
      ; sub⊆f = λ u′v′∈sub → there (sub⊆f u′v′∈sub)
      ; pre⊑w = pre⊑w
      ; allSmalleru = lemma
      }
      where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → u′ ⊑ w → (u′ , v′) ∈ sub
            lemma here u′⊑w = ¬-elim (¬u⊑w u′⊑w)
            lemma (there u′v′∈f′) u′⊑w = allSmalleru u′v′∈f′ u′⊑w

isLargest' : ∀ {i} → {f : FinFun {i}} → conFinFun f → {w : Nbh {i}} → (lrg : Largest f w) →
             {g : FinFun {i}} → g ⊆ f → (∀ {u v} → (u , v) ∈ g → u ⊑ w) →
             ∀ {u v} → (u , v) ∈ g → v ⊑ post (Largest.sub lrg)
isLargest' conf record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru } g⊆f p uv∈g
  = lemma (allSmalleru (g⊆f uv∈g) (p uv∈g)) (coherence (subsetIsCon sub⊆f conf) (⊠-fst (orderOnlyCon pre⊑w)))
  where lemma : ∀ {i} → {f : FinFun {i}} → {u v : Nbh {i}} → (u , v) ∈ f → con (post f) → v ⊑ post f
        lemma here conpostf = ⊑-⊔-fst conpostf
        lemma {f = (u′ , v′) ∷ f′} (there uv∈f′) conpostf
          = ⊑-⊔-lemma₂ (lemma uv∈f′ (conLemma₂ {u = v′} conpostf)) conpostf

isLargest : ∀ {i} → {f : FinFun {i}} → conFinFun f → {w : Nbh {i}} → {con w} → (lrg : Largest f w) →
            {g : FinFun {i}} → g ⊆ f → (∀ {u v} → (u , v) ∈ g → u ⊑ w) →
            post g ⊑ post (Largest.sub lrg)
isLargest conf record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru } {g = ∅} _ _
  = ⊑-bot (coherence (subsetIsCon sub⊆f conf) (⊠-fst (orderOnlyCon pre⊑w)))
isLargest conf {w} {conw} lrg {g = (u , v) ∷ g′} g⊆f p
  = ⊑-⊔ (isLargest' conf lrg g⊆f p here)
        (isLargest conf {w} {conw} lrg (⊆-lemma₂ g⊆f) (λ u′v′∈g′ → p (there u′v′∈g′)))
        (coherence (subsetIsCon g⊆f conf) (Con-⊔ {u = u} {pre g′} {w} {!!} {!!}))

test : ∀ {i} → {f g : FinFun {i}} → (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (u ⊑ u′)) →
       Decidable ((F f) ⊑ (F g))
test = {!!}
-- For every (u , v) ∈ g, if F f ⊑ (F (largest g u)) then (and only then) is F f ⊑ F g.
-- One direction is easy: F (largest g u) ⊑ F g since it is a subset of g, and by transitivity F f ⊑ F g.
-- For the other direction, if F f ⊑ F g, then F f ⊑ (F (largest g u)) by transitivity, because F sub ⊑ F (largest g u)
-- for any sub ⊆ g such that (pre sub) ⊑ w.

relationDecidable : ∀ {i} → {u v : Nbh {i}} → Decidable (u ⊑ v)
relationDecidable {u = ⊥} {v} with (consistencyDecidable {u = v})
... | inl conv = inl (⊑-bot conv)
... | inr ¬conv = inr lemma
  where lemma : ¬ (⊥ ⊑ v)
        lemma (⊑-bot conv) = ¬conv conv
relationDecidable {u = 0ᵤ} {v} = {!!}
relationDecidable {u = s u} {v} = {!!}
relationDecidable {u = ℕ} {v} = {!!}
relationDecidable {u = F f} {⊥} = {!!}
relationDecidable {u = F f} {0ᵤ} = {!!}
relationDecidable {u = F f} {s v} = {!!}
relationDecidable {u = F f} {ℕ} = {!!}
relationDecidable {u = F f} {F g} = test {f = f} {g} (\{u} {v} {u′} {v} _ _ → relationDecidable {u = u} {u′})
relationDecidable {u = F f} {refl v} = {!!}
relationDecidable {u = F f} {I v v₁ v₂} = {!!}
relationDecidable {u = F f} {Π v x₁} = {!!}
relationDecidable {u = F f} {𝒰} = {!!}
relationDecidable {u = F f} {incons} = {!!}
relationDecidable {u = refl u} {v} = {!!}
relationDecidable {u = I U u u′} {v} = {!!}
relationDecidable {u = Π u f} {v} = {!!}
relationDecidable {u = 𝒰} {v} = {!!}
relationDecidable {u = incons} {v} = {!!}
