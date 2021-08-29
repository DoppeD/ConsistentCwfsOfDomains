--{-# OPTIONS --safe #-}

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
con' ⊥ _ = 𝟙
con' 0ᵤ _ = 𝟙
con' (s u) as = con' u as
con' ℕ _ = 𝟙
con' (F f) (acc rs) =
  (∀ {u v u′ v′} → (uv∈f : (u , v) ∈ f) → (u′v′∈f : (u′ , v′) ∈ f) →
  con' (u ⊔ u′) (rs _ (s≤s (uvu′v′∈f⇒u⊔u′≤f uv∈f u′v′∈f))) → con' (v ⊔ v′) (rs _ (s≤s (uvu′v′∈f⇒v⊔v′≤f uv∈f u′v′∈f)))
  ) ⊠ (∀ {u v} → (uv∈f : (u , v) ∈ f) → con' u (rs _ (s≤s (uv∈f⇒u≤f f u v uv∈f))) ⊠ con' v (rs _ (s≤s (uv∈f⇒v≤f f u v uv∈f))))
con' (refl u) as = con' u as
con' (I U u u′) (acc rs) =
  con' U (rs _ (s≤s (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _))))
  ⊠
  (con' u (rs _ (s≤s (≤-trans (n≤m⊔n (assignSize U) _) (m≤m⊔n _ _))))
   ⊠
   con' u′ (rs _ (s≤s (n≤m⊔n _ _)))
  )
con' (Π U f) (acc rs) =
  con' U (rs _ (s≤s (m≤m⊔n _ _))) ⊠
  (∀ {u v u′ v′} → (uv∈f : (u , v) ∈ f) → (u′v′∈f : (u′ , v′) ∈ f) →
   con' (u ⊔ u′) (rs _ (s≤s (≤-trans (uvu′v′∈f⇒u⊔u′≤f uv∈f u′v′∈f) (n≤m⊔n _ _)))) →
   con' (v ⊔ v′) (rs _ (s≤s (≤-trans (uvu′v′∈f⇒v⊔v′≤f uv∈f u′v′∈f) (n≤m⊔n _ _))))
  )
con' 𝒰 _ = 𝟙
con' incons _ = 𝟘

con : Nbh → Set
con u = con' u (<-wellFounded (assignSize u))
