{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.RelationDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.ConsistencyDecidable
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation

test : ∀ {i} → {f g : FinFun {i}} → (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (u ⊑ u′)) →
       Decidable ((F f) ⊑ (F g))
test = {!!}

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
