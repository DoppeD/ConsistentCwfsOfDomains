module Cwf.DomainCwf.UniType.MembershipDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.DecidableEquality
open import Cwf.DomainCwf.UniType.FinFun

open import Agda.Builtin.Equality

membershipDecidable : ∀ {i} → {f : FinFun {i}} → {u v : Nbh {i}} → Decidable ((u , v) ∈ f)
membershipDecidable {f = ∅} {u} {v} = inr xy∈∅-abs
membershipDecidable {f = _ ∷ f′} {u} {v} with membershipDecidable {f = f′} {u} {v}
membershipDecidable {f = _ ∷ f′} {u} {v} | inl uv∈f′ = inl (there uv∈f′)
membershipDecidable {f = (u′ , v′) ∷ _} {u} {v} | inr _
  with (decidableEquality {u = u} {u′}) | decidableEquality {u = v} {v′}
membershipDecidable | inr ¬uv∈f′ | inl refl | inl refl = inl here
membershipDecidable {f = (u′ , v′) ∷ f′} {u} {v} | inr ¬uv∈f′ | inl refl | inr ¬v≡v′ = inr lemma
  where lemma : ¬ ((u , v) ∈ ((u′ , v′) ∷ f′))
        lemma here = ¬v≡v′ refl
        lemma (there uv∈f′) = ¬uv∈f′ uv∈f′
membershipDecidable {f = (u′ , v′) ∷ f′} {u} {v} | inr ¬uv∈f′ | inr ¬u≡u′ | _ = inr lemma
  where lemma : ¬ ((u , v) ∈ ((u′ , v′) ∷ f′))
        lemma here = ¬u≡u′ refl
        lemma (there uv∈f′) = ¬uv∈f′ uv∈f′
