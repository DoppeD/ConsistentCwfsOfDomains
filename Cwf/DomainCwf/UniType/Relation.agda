{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.Relation where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.AssignSize
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition

open import Data.Nat.Base hiding (ℕ ; _⊔_)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded

record ⊑-proof (g : FinFun Nbh Nbh) (u v : Nbh) : Set
data _⊑_ : (u v : Nbh) → Set

record ⊑-proof g u v where
  inductive
  field
    sub : FinFun Nbh Nbh
    sub⊆g : sub ⊆ g
    pre⊑u : pre sub ⊑ u
    v⊑post : v ⊑ post sub

data _⊑_ where
  ⊑-bot : ∀ {u} → con u → ⊥ ⊑ u
  ⊑-0 : 0ᵤ ⊑ 0ᵤ
  ⊑-s : ∀ {u v} → u ⊑ v → s u ⊑ s v
  ⊑-ℕ : ℕ ⊑ ℕ
  ⊑-F : ∀ {f g} → (conf : conFinFun f) → (cong : conFinFun g) →
        (∀ {u v} → (u , v) ∈ f → ⊑-proof g u v) →
        F f ⊑ F g
  ⊑-rfl : ∀ {u v} → u ⊑ v → refl u ⊑ refl v
  ⊑-I : ∀ {U u v U′ u′ v′} → U ⊑ U′ → u ⊑ u′ → v ⊑ v′ → I U u v ⊑ I U′ u′ v′
  ⊑-Π : ∀ {u v f g} → u ⊑ v → F f ⊑ F g → Π u f ⊑ Π v g
  ⊑-𝒰 : 𝒰 ⊑ 𝒰

orderOnlyCon' : ∀ {u v p q} → u ⊑ v → con' u p ⊠ con' v q
orderOnlyCon' {v = v} (⊑-bot conv) = * , wfIrrelevant {v} conv
orderOnlyCon' ⊑-0 = * , *
orderOnlyCon' {s u} {s v} {acc _} {acc _} (⊑-s u⊑v)
  with (orderOnlyCon' {u} {v} {<-wellFounded _} {<-wellFounded _} u⊑v)
... | conu , conv = wfIrrelevant {u} conu , wfIrrelevant {v} conv
orderOnlyCon' ⊑-ℕ = * , *
orderOnlyCon' {F f} {F g} {acc _} {acc _} (⊑-F conf cong p)
  = {!!} , {!!}
orderOnlyCon' {refl u} {refl v} {acc _} {acc _} (⊑-rfl u⊑v)
  with (orderOnlyCon' {u} {v} {<-wellFounded _} {<-wellFounded _} u⊑v)
... | conu , conv = wfIrrelevant {u} conu , wfIrrelevant {v} conv
orderOnlyCon' (⊑-Π {u} {v} u⊑v f⊑g) = {!!}
orderOnlyCon' (⊑-I U⊑U′ u⊑u′ v⊑v′) = {!!}
orderOnlyCon' ⊑-𝒰 = * , *

-- Ordering is only defined for consistent neighborhoods
orderOnlyCon : ∀ {u v} → u ⊑ v → con u ⊠ con v
orderOnlyCon = orderOnlyCon'
