{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.Relation where

open import Base.Core
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun

open import Agda.Builtin.Size

record ⊑-proof {i : Size} (g : FinFun {i}) (u v : Nbh {i}) : Set
data _⊑_ : ∀ {i} → (u v : Nbh {i}) → Set

record ⊑-proof {i} g u v where
  inductive
  field
    sub : FinFun {i}
    sub⊆g : sub ⊆ g
    pre⊑u : pre sub ⊑ u
    v⊑post : v ⊑ post sub

data _⊑_ where
  ⊑-bot : ∀ {i} → {u : Nbh {i}} → con u → ⊥ ⊑ u
  ⊑-0 : 0ᵤ ⊑ 0ᵤ
  ⊑-s : ∀ {i} → {u v : Nbh {i}} → u ⊑ v → s u ⊑ s v
  ⊑-ℕ : ℕ ⊑ ℕ
  ⊑-F : ∀ {i} → {f g : FinFun {i}} → (conf : conFinFun f) → (cong : conFinFun g) →
        (∀ {u v} → (u , v) ∈ f → ⊑-proof g u v) →
        F f ⊑ F g
  ⊑-rfl : ∀ {i} → {u v : Nbh {i}} → u ⊑ v → refl u ⊑ refl v
  ⊑-I : ∀ {i} → {U u v U′ u′ v′ : Nbh {i}} → U ⊑ U′ → u ⊑ u′ → v ⊑ v′ → I U u v ⊑ I U′ u′ v′
  ⊑-Π : ∀ {i} → {u v : Nbh {i}} → {f g : FinFun {i}} → u ⊑ v → F f ⊑ F g → Π u f ⊑ Π v g
  ⊑-𝒰 : 𝒰 ⊑ 𝒰

-- Ordering is only defined for consistent neighborhoods
orderOnlyCon : ∀ {i} → {u v : Nbh {i}} → u ⊑ v → con u ⊠ con v
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
