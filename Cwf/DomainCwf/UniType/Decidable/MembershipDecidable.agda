module Cwf.DomainCwf.UniType.Decidable.MembershipDecidable where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Decidable.EqualityDecidable
open import Cwf.DomainCwf.UniType.Definition

open import Agda.Builtin.Equality

membershipDecidable : ∀ {f u v} → Decidable ((u , v) ∈ f)
membershipDecidable {∅} {u} {v} = inr xy∈∅-abs
membershipDecidable {_ ∷ f′} {u} {v} with membershipDecidable {f′} {u} {v}
membershipDecidable {_ ∷ f′} {u} {v} | inl uv∈f′ = inl (there uv∈f′)
membershipDecidable {(u′ , v′) ∷ _} {u} {v} | inr _
  with (equalityDecidable {u = u} {u′}) | equalityDecidable {u = v} {v′}
membershipDecidable | inr ¬uv∈f′ | inl refl | inl refl = inl here
membershipDecidable {(u′ , v′) ∷ f′} {u} {v} | inr ¬uv∈f′ | inl refl | inr ¬v≡v′ = inr lemma
  where lemma : ¬ ((u , v) ∈ ((u′ , v′) ∷ f′))
        lemma here = ¬v≡v′ refl
        lemma (there uv∈f′) = ¬uv∈f′ uv∈f′
membershipDecidable {(u′ , v′) ∷ f′} {u} {v} | inr ¬uv∈f′ | inr ¬u≡u′ | _ = inr lemma
  where lemma : ¬ ((u , v) ∈ ((u′ , v′) ∷ f′))
        lemma here = ¬u≡u′ refl
        lemma (there uv∈f′) = ¬uv∈f′ uv∈f′
