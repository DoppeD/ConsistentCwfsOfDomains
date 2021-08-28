--{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.Relation where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition

record ⊑-proof (g : FinFun) (u v : Nbh) : Set
data _⊑_ : (u v : Nbh) → Set

record ⊑-proof g u v where
  inductive
  field
    sub : FinFun
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

-- Ordering is only defined for consistent neighborhoods
orderOnlyCon : ∀ {u v} → u ⊑ v → con u ⊠ con v
orderOnlyCon (⊑-bot conu) = * , conu
orderOnlyCon ⊑-0 = * , *
orderOnlyCon (⊑-s u⊑v) = orderOnlyCon u⊑v
orderOnlyCon ⊑-ℕ = * , *
orderOnlyCon (⊑-F conf cong f) = conf , cong
orderOnlyCon (⊑-rfl u⊑v) = orderOnlyCon u⊑v
orderOnlyCon (⊑-Π u⊑v f⊑g) with (orderOnlyCon u⊑v) | orderOnlyCon f⊑g
... | conu , conv | conf , cong = ( conu , conf ) , ( conv , cong )
orderOnlyCon (⊑-I U⊑U′ u⊑u′ v⊑v′)
  with (orderOnlyCon U⊑U′) | orderOnlyCon u⊑u′ | orderOnlyCon v⊑v′
... | conU , conU′ | conu , conu′ | conv , conv′
  = (conU , (conu , conv)) , (conU′ , (conu′ , conv′))
orderOnlyCon ⊑-𝒰 = * , *
