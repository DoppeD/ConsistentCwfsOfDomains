{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.RelationDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.AxiomProofs
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyDecidable
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation

open import Agda.Builtin.Size

-- Prove:
-- ∀ {u v} → (u , v) ∈ f → u ⊑ w → (u , v) ∈ largest f w conw p
-- ∀ {u v} → (u , v) ∈ f → (u , v) ∈ largest f w conw p → u ⊑ w (this just follows from pre sub ⊑ w)
-- So largest f w conw p contains exactly the pairs (u , v) such that u ⊑ w.
-- Also need ∀ {f u v) → Decidable ((u , v) ∈ f)
-- And ∀ {u v} → (u , v) ∈ f → ¬ ((u , v) ∈ largest f w conw p) → ¬ (u ⊑ w) (shouldn't be needed)
-- Then show that any sub ⊆ f such that pre sub ⊑ u satisifes sub ⊆ largest f w conw p.
-- Then post (sub) ⊑ post (largest f w conw p) by Ω (since F sub ⊑ F (largest f w conw p))

record Largest {i : Size} (f : FinFun {i}) (w : Nbh {i}) : Set where
  field
    sub : FinFun {i}
    sub⊆f : sub ⊆ f
    pre⊑w : pre sub ⊑ w
    isLargest : {u v : Nbh {i}} → (u , v) ∈ f → u ⊑ w → (u , v) ∈ sub

largest : ∀ {i} → (f : FinFun {i}) → (w : Nbh {i}) → con w →
          (∀ {u v} → (u , v) ∈ f → Decidable (u ⊑ w)) →
          Largest f w
largest {i} ∅ w conw _ =
  record
    { sub = ∅
    ; sub⊆f = ∅-isSubset
    ; pre⊑w = ⊑-bot conw
    ; isLargest = {!!}
    }
largest ((u , v) ∷ f′) w conw p
  with (p here) | largest f′ w conw λ u′v′∈f′ → p (there u′v′∈f′)
... | inl u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w }
  = record
      { sub = (u , v) ∷ sub
      ; sub⊆f = ⊆-lemma₄ here (λ u′v′∈sub → there (sub⊆f u′v′∈sub))
      ; pre⊑w = ⊑-⊔ u⊑w pre⊑w (Con-⊔ u⊑w pre⊑w)
      ; isLargest = {!!}
      }
... | inr ¬u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w }
  = record
      { sub = sub
      ; sub⊆f = λ u′v′∈sub → there (sub⊆f u′v′∈sub)
      ; pre⊑w = pre⊑w
      ; isLargest = {!!}
      }

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
