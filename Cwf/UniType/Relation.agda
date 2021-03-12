module Cwf.UniType.Relation where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition

record Thingy (g : FinFun Nbh Nbh) (u v : Nbh) : Set
data _⊑_ : (u v : Nbh) → Set

record Thingy g u v where
  inductive
  field
    sub : FinFun Nbh Nbh
    preable : con (pre sub)
    sub⊆g : sub ⊆ g
    pre⊑u : pre sub ⊑ u
    v⊑post : v ⊑ post sub

data _⊑_ where
  ⊑-refl : ∀ {u} → con u → u ⊑ u
  ⊑-⊥ : ∀ {u} → con u → ⊥ ⊑ u
  ⊑-s : ∀ {u v} → u ⊑ v → s u ⊑ s v
  ⊑-F : ∀ {f g} → (conf : conFinFun f) → (cong : conFinFun g) →
        (∀ u v → (u , v) ∈ f → Thingy g u v) →
        F f ⊑ F g
  ⊑-Π : ∀ {u v f g} → u ⊑ v → F f ⊑ F g → Π u f ⊑ Π v g

-- Ordering is only defined for consistent neighborhoods
orderOnlyCon : ∀ {u v} → u ⊑ v → con u ⊠ con v
orderOnlyCon (⊑-refl conu) = conu , conu
orderOnlyCon (⊑-⊥ conu) = * , conu
orderOnlyCon (⊑-s u⊑v) = orderOnlyCon u⊑v
orderOnlyCon (⊑-F conf cong f) = conf , cong
orderOnlyCon (⊑-Π u⊑v f⊑g) with (orderOnlyCon u⊑v) | orderOnlyCon f⊑g
... | conu , conv | conf , cong = ( conu , conf ) , ( conv , cong )
