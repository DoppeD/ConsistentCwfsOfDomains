{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.ConsistencyTerminating where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.AssignSize
open import Cwf.DomainCwf.UniType.Definition

open import Data.Nat.Base renaming (_⊔_ to max ; ℕ to Nat)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded

-- These definitions are exactly the same as in Consistency, except that
-- they carry with them an accessibility predicate. This allows them to
-- pass Agda's termination checker.
-- See the AssignSize module for details on how natural numbers are assigned to neihborhoods.
-- Note that the definitions do not depend computationally on this predicate.
conFinFun : ∀ f → (∀ u → assignSize u < assignSize (F f) → Set) → Set
conFinFun f con =
  (∀ {u v u′ v′} → (uv∈f : (u , v) ∈ f) → (u′v′∈f : (u′ , v′) ∈ f) →
    con (u ⊔ u′) (s≤s (uvu′v′∈f⇒u⊔u′≤f uv∈f u′v′∈f)) →
    con (v ⊔ v′) (s≤s (uvu′v′∈f⇒v⊔v′≤f uv∈f u′v′∈f))
  ) ⊠
  (∀ {u v} → (uv∈f : (u , v) ∈ f) → con u (s≤s (uv∈f⇒u≤f f u v uv∈f)) ⊠ con v (s≤s (uv∈f⇒v≤f f u v uv∈f)))

con : ∀ u → Acc _<_ (assignSize u) → Set
con ⊥ _ = 𝟙
con 0ᵤ _ = 𝟙
con (s u) (acc rs) = con u (rs _ (s≤s ≤-refl))
con ℕ _ = 𝟙
con (F f) (acc rs) = conFinFun f λ u u<Ff → con u (rs _ u<Ff)
con (refl u) (acc rs) = con u (rs _ (s≤s ≤-refl))
con (I U u u′) (acc rs) =
  con U (rs _ U<IUuu′) ⊠ (con u (rs _ (u<IUuu′ {U})) ⊠ con u′ (rs _ (u′<IUuu′ {U})))
con (Π U f) (acc rs) =
  con U (rs _ (s≤s (m≤m⊔n _ _))) ⊠ conFinFun f λ u u<Ff → con u (rs _ (<-trans u<Ff (s≤s (m≤n⊔m _ _))))
con 𝒰 _ = 𝟙
con incons _ = 𝟘

-- Consistency does not depend on which proof of irrelevance is provided.
wfIrrelevant : ∀ {u p q} → con u p → con u q
wfIrrelevant {⊥} _ = *
wfIrrelevant {0ᵤ} {acc _} {acc _} _ = *
wfIrrelevant {s u} {acc _} {acc _} conu = wfIrrelevant {u} conu
wfIrrelevant {ℕ} {acc _} {acc _} _ = *
wfIrrelevant {F f} {acc _} {acc _} (conPairsf , conElemsf)
  = (λ {u} {v} {u′} {v′} uv∈f u′v′∈f conuu′ → wfIrrelevant {v ⊔ v′} (conPairsf uv∈f u′v′∈f (wfIrrelevant {u ⊔ u′} conuu′)))
  , (λ {u} {v} uv∈f → wfIrrelevant {u} (⊠-fst (conElemsf uv∈f)) , wfIrrelevant {v} (⊠-snd (conElemsf uv∈f)))
wfIrrelevant {refl u} {acc _} {acc _} conu = wfIrrelevant {u} conu
wfIrrelevant {I U u u′} {acc _} {acc _} (conU , (conu , conu′))
  = wfIrrelevant {U} conU , (wfIrrelevant {u} conu , wfIrrelevant {u′} conu′)
wfIrrelevant {Π U f} {acc _} {acc _} (conU , (conPairsf , conElemsf))
  = (wfIrrelevant {U} conU) ,
    ((λ {u} {v} {u′} {v′} uv∈f u′v′∈f conuu′ → wfIrrelevant {v ⊔ v′} (conPairsf uv∈f u′v′∈f (wfIrrelevant {u ⊔ u′} conuu′)))
  , (λ {u} {v} uv∈f → wfIrrelevant {u} (⊠-fst (conElemsf uv∈f)) , wfIrrelevant {v} (⊠-snd (conElemsf uv∈f))))
wfIrrelevant {𝒰} {acc _} {acc _} _ = *
