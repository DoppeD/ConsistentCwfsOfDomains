{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.Consistency where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.AssignSize
open import Cwf.DomainCwf.UniType.Definition

open import Data.Nat.Base renaming (_⊔_ to max ; ℕ to Nat)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded

con' : ∀ u → Acc _<_ (assignSize u) → Set
conFinFun' : ∀ f → Acc _<_ (assignSize (F f)) → Set
con' ⊥ _ = 𝟙
con' 0ᵤ _ = 𝟙
con' (s u) (acc rs) = con' u (rs _ (s≤s ≤-refl))
con' ℕ _ = 𝟙
con' (F f) (acc rs) = conFinFun' f (acc rs)
con' (refl u) (acc rs) = con' u (rs _ (s≤s ≤-refl))
con' (I U u u′) (acc rs) =
  con' U (rs _ (s≤s (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _))))
  ⊠
  (con' u (rs _ (s≤s (≤-trans (m≤n⊔m (assignSize U) _) (m≤m⊔n _ _))))
   ⊠
   con' u′ (rs _ (s≤s (m≤n⊔m _ _)))
  )
con' (Π U f) (acc rs) =
  con' U (rs _ (s≤s (m≤m⊔n _ _))) ⊠ conFinFun' f (rs _ (s≤s (m≤n⊔m _ _)))
con' 𝒰 _ = 𝟙
con' incons _ = 𝟘

conFinFun' f (acc rsf) =
  (∀ {u v u′ v′} → (uv∈f : (u , v) ∈ f) → (u′v′∈f : (u′ , v′) ∈ f) →
    con' (u ⊔ u′) (rsf _ (s≤s (uvu′v′∈f⇒u⊔u′≤f uv∈f u′v′∈f))) →
    con' (v ⊔ v′) (rsf _ (s≤s (uvu′v′∈f⇒v⊔v′≤f uv∈f u′v′∈f)))
  ) ⊠
  (∀ {u v} → (uv∈f : (u , v) ∈ f) → con' u (rsf _ (s≤s (uv∈f⇒u≤f f u v uv∈f))) ⊠ con' v (rsf _ (s≤s (uv∈f⇒v≤f f u v uv∈f))))


con : Nbh → Set
con u = con' u (<-wellFounded (assignSize u))

conFinFun : FinFun Nbh Nbh → Set
conFinFun f = conFinFun' f (<-wellFounded (suc (assignSizeFun f)))

wfIrrelevant : ∀ {u p q} → con' u p → con' u q
wfIrrelevant' : {f : FinFun Nbh Nbh} → ∀ {p q} → conFinFun' f p → conFinFun' f q

wfIrrelevant {⊥} x = *
wfIrrelevant {0ᵤ} {acc rs} {acc rs₁} x = *
wfIrrelevant {s u} {acc rs} {acc rs₁} x = wfIrrelevant {u} x
wfIrrelevant {ℕ} {acc rs} {acc rs₁} x = *
wfIrrelevant {F f} {acc rs} {acc rs₁} confp = wfIrrelevant' {f} {acc rs} {acc rs₁} confp
wfIrrelevant {refl u} {acc rs} {acc rs₁} x = wfIrrelevant {u} x
wfIrrelevant {I u u₁ u₂} {acc rs} {acc rs₁} (x , (x₁ , x₂)) = (wfIrrelevant {u} x) , ((wfIrrelevant {u₁} x₁) , (wfIrrelevant {u₂} x₂))
wfIrrelevant {Π u f} {acc rs} {acc rs₁} (x , x₂) = wfIrrelevant {u} x , (wfIrrelevant' x₂)
wfIrrelevant {𝒰} {acc rs} {acc rs₁} x = *

wfIrrelevant' {f} {acc rs} {acc rs₁} (x , x₁)
  = (λ {u} {v} {u′} {v′} uv∈f u′v′∈f conuu′ → wfIrrelevant {v ⊔ v′} (x uv∈f u′v′∈f (wfIrrelevant {u ⊔ u′} conuu′)))
  , (λ {u} {v} uv∈f → wfIrrelevant {u} (⊠-fst (x₁ uv∈f)) , wfIrrelevant {v} (⊠-snd (x₁ uv∈f)))
