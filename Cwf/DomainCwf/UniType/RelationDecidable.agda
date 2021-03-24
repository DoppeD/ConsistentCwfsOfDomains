{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.RelationDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation

test : ∀ {i} → {f g : FinFun {i}} → (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (u ⊑ u′)) → Decidable ((F f) ⊑ (F g))
test = {!!}

relationDecidable : ∀ {i} → {u v : Nbh {i}} → Decidable (u ⊑ v)
relationDecidable {u = ⊥} {v} = inl (⊑-bot {!!})
relationDecidable {u = 0ᵤ} {v} = {!!}
relationDecidable {u = s u} {v} = {!!}
relationDecidable {u = ℕ} {v} = {!!}
relationDecidable {u = F x} {⊥} = {!!}
relationDecidable {u = F x} {0ᵤ} = {!!}
relationDecidable {u = F x} {s v} = {!!}
relationDecidable {u = F x} {ℕ} = {!!}
relationDecidable {u = F f} {F g} = test {f = f} {g} (\{u} {v} {u′} {v} _ _ → relationDecidable {u = u} {u′})
relationDecidable {u = F x} {refl v} = {!!}
relationDecidable {u = F x} {I v v₁ v₂} = {!!}
relationDecidable {u = F x} {Π v x₁} = {!!}
relationDecidable {u = F x} {𝒰} = {!!}
relationDecidable {u = F x} {incons} = {!!}
relationDecidable {u = refl u} {v} = {!!}
relationDecidable {u = I u u₁ u₂} {v} = {!!}
relationDecidable {u = Π u x} {v} = {!!}
relationDecidable {u = 𝒰} {v} = {!!}
relationDecidable {u = incons} {v} = {!!}
