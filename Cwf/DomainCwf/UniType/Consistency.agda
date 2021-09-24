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

conFinFun' : ∀ f → (∀ u → assignSize u < assignSize (F f) → Set) → Set
conFinFun' f con =
  (∀ {u v u′ v′} → (uv∈f : (u , v) ∈ f) → (u′v′∈f : (u′ , v′) ∈ f) →
    con (u ⊔ u′) (s≤s (uvu′v′∈f⇒u⊔u′≤f uv∈f u′v′∈f)) →
    con (v ⊔ v′) (s≤s (uvu′v′∈f⇒v⊔v′≤f uv∈f u′v′∈f))
  ) ⊠
  (∀ {u v} → (uv∈f : (u , v) ∈ f) → con u (s≤s (uv∈f⇒u≤f f u v uv∈f)) ⊠ con v (s≤s (uv∈f⇒v≤f f u v uv∈f)))

con' : ∀ u → Acc _<_ (assignSize u) → Set
con' ⊥ _ = 𝟙
con' 0ᵤ _ = 𝟙
con' (s u) (acc rs) = con' u (rs _ (s≤s ≤-refl))
con' ℕ _ = 𝟙
con' (F f) (acc rs) = conFinFun' f λ u u<Ff → con' u (rs _ u<Ff)
con' (refl u) (acc rs) = con' u (rs _ (s≤s ≤-refl))
con' (I U u u′) (acc rs) =
  con' U (rs _ U<IUuu′) ⊠ (con' u (rs _ (u<IUuu′ {U})) ⊠ con' u′ (rs _ (u′<IUuu′ {U})))
con' (Π U f) (acc rs) =
  con' U (rs _ (s≤s (m≤m⊔n _ _))) ⊠ conFinFun' f λ u u<Ff → con' u (rs _ (<-trans u<Ff (s≤s (m≤n⊔m _ _))))
con' 𝒰 _ = 𝟙
con' incons _ = 𝟘

con : Nbh → Set
con u = con' u (<-wellFounded (assignSize u))

conFinFun : FinFun Nbh Nbh → Set
conFinFun f = conFinFun' f λ u _ → con u

wfIrrelevant : ∀ {u p q} → con' u p → con' u q
wfIrrelevant {⊥} x = *
wfIrrelevant {0ᵤ} {acc rs} {acc rs₁} x = *
wfIrrelevant {s u} {acc rs} {acc rs₁} x = wfIrrelevant {u} x
wfIrrelevant {ℕ} {acc rs} {acc rs₁} x = *
wfIrrelevant {F f} {acc rs} {acc rs₁} (x , x₁)
  = (λ {u} {v} {u′} {v′} uv∈f u′v′∈f conuu′ → wfIrrelevant {v ⊔ v′} (x uv∈f u′v′∈f (wfIrrelevant {u ⊔ u′} conuu′)))
  , (λ {u} {v} uv∈f → wfIrrelevant {u} (⊠-fst (x₁ uv∈f)) , wfIrrelevant {v} (⊠-snd (x₁ uv∈f)))
wfIrrelevant {refl u} {acc rs} {acc rs₁} x = wfIrrelevant {u} x
wfIrrelevant {I u u₁ u₂} {acc rs} {acc rs₁} (x , (x₁ , x₂)) = (wfIrrelevant {u} x) , ((wfIrrelevant {u₁} x₁) , (wfIrrelevant {u₂} x₂))
wfIrrelevant {Π u f} {acc rs} {acc rs₁} (a , (x , x₁))
  = (wfIrrelevant {u} a) ,
    ((λ {u} {v} {u′} {v′} uv∈f u′v′∈f conuu′ → wfIrrelevant {v ⊔ v′} (x uv∈f u′v′∈f (wfIrrelevant {u ⊔ u′} conuu′)))
  , (λ {u} {v} uv∈f → wfIrrelevant {u} (⊠-fst (x₁ uv∈f)) , wfIrrelevant {v} (⊠-snd (x₁ uv∈f))))
wfIrrelevant {𝒰} {acc rs} {acc rs₁} x = *

wfIrrelevantPairs : ∀ {f u v u′ v′ p q r s} → (u , v) ∈ f → (u′ , v′) ∈ f →
                    (con' (u ⊔ u′) p → con' (v ⊔ v′) q) →
                    con' (u ⊔ u′) r → con' (v ⊔ v′) s
wfIrrelevantPairs {u = u} {v} {u′} {v′} uv∈f u′v′∈f f conuu′
  = wfIrrelevant {v ⊔ v′} (f (wfIrrelevant {u ⊔ u′} conuu′))

wfIrrelevantElems : ∀ {f u v p q r s} → (u , v) ∈ f → con' u p ⊠ con' v q →
                    con' u r ⊠ con' v s
wfIrrelevantElems {u = u} {v} uv∈f (conu , conv)
  = wfIrrelevant {u} conu , wfIrrelevant {v} conv
