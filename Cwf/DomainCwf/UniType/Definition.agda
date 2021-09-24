{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.Definition where

open import Base.Core
open import Base.FinFun

-- One of our "proto-neighborhoods" is incons, which represent an inconsistent
-- neighborhood. Such a neighborhood is the result of taking the supremum
-- of two neighborhoods that are not mutually consistent, such as 0ᵤ and 𝒰.
-- When instantiating our neighborhood system in the Instance module, we
-- only consider those neighborhoods below that are consistent as actual
-- neighborhoods.
data Nbh : Set where
  ⊥ : Nbh
  0ᵤ : Nbh
  s : Nbh → Nbh
  ℕ : Nbh
  F : FinFun Nbh Nbh → Nbh
  refl : Nbh → Nbh
  I : Nbh → Nbh → Nbh → Nbh
  Π : Nbh → FinFun Nbh Nbh → Nbh
  𝒰 : Nbh
  incons : Nbh

-- The supremum operator could also be defined as a constructor of the Nbh type,
-- but that is arguably more difficult to work with.
_⊔_ : Nbh → Nbh → Nbh
⊥ ⊔ u = u
0ᵤ ⊔ ⊥ = 0ᵤ
0ᵤ ⊔ 0ᵤ = 0ᵤ
0ᵤ ⊔ (s _) = incons
0ᵤ ⊔ ℕ = incons
0ᵤ ⊔ (F _) = incons
0ᵤ ⊔ (refl _) = incons
0ᵤ ⊔ (I _ _ _) = incons
0ᵤ ⊔ (Π _ _) = incons
0ᵤ ⊔ 𝒰 = incons
0ᵤ ⊔ incons = incons
(s u) ⊔ ⊥ = s u
(s _) ⊔ 0ᵤ = incons
(s u) ⊔ (s v) = s (u ⊔ v)
(s _) ⊔ ℕ = incons
(s _) ⊔ (F _) = incons
(s _) ⊔ (refl _) = incons
(s _) ⊔ (I _ _ _) = incons
(s _) ⊔ (Π _ _) = incons
(s _) ⊔ 𝒰 = incons
(s _) ⊔ incons = incons
ℕ ⊔ ⊥ = ℕ
ℕ ⊔ 0ᵤ = incons
ℕ ⊔ (s _) = incons
ℕ ⊔ ℕ = ℕ
ℕ ⊔ (F _) = incons
ℕ ⊔ (refl _) = incons
ℕ ⊔ (I _ _ _) = incons
ℕ ⊔ (Π _ _) = incons
ℕ ⊔ 𝒰 = incons
ℕ ⊔ incons = incons
(F f) ⊔ ⊥ = F f
(F _) ⊔ 0ᵤ = incons
(F _) ⊔ (s _) = incons
(F _) ⊔ ℕ = incons
(F f) ⊔ (F g) = F (f ∪ g)
(F _) ⊔ (refl _) = incons
(F _) ⊔ (I _ _ _) = incons
(F _) ⊔ (Π _ _) = incons
(F _) ⊔ 𝒰 = incons
(F _) ⊔ incons = incons
(refl u) ⊔ ⊥ = refl u
(refl u) ⊔ 0ᵤ = incons
(refl u) ⊔ (s _) = incons
(refl u) ⊔ ℕ = incons
(refl u) ⊔ (F _) = incons
(refl u) ⊔ (refl v) = refl (u ⊔ v)
(refl u) ⊔ (I _ _ _) = incons
(refl u) ⊔ (Π _ _) = incons
(refl u) ⊔ 𝒰 = incons
(refl u) ⊔ incons = incons
(I U u v) ⊔ ⊥ = I U u v
(I _ _ _) ⊔ 0ᵤ = incons
(I _ _ _) ⊔ (s _) = incons
(I _ _ _) ⊔ ℕ = incons
(I _ _ _) ⊔ (F _) = incons
(I _ _ _) ⊔ (refl _) = incons
(I U u v) ⊔ (I U′ u′ v′) = I (U ⊔ U′) (u ⊔ u′) (v ⊔ v′)
(I _ _ _) ⊔ (Π _ _) = incons
(I _ _ _) ⊔ 𝒰 = incons
(I _ _ _) ⊔ incons = incons
(Π u f) ⊔ ⊥ = Π u f
(Π _ _) ⊔ 0ᵤ = incons
(Π _ _) ⊔ (s _) = incons
(Π _ _) ⊔ ℕ = incons
(Π _ _) ⊔ (F _) = incons
(Π _ _) ⊔ (I _ _ _) = incons
(Π u f) ⊔ (Π v g) = Π (u ⊔ v) (f ∪ g)
(Π _ _) ⊔ 𝒰 = incons
(Π _ _) ⊔ (refl _) = incons
(Π _ _) ⊔ incons = incons
𝒰 ⊔ ⊥ = 𝒰
𝒰 ⊔ 0ᵤ = incons
𝒰 ⊔ (s _) = incons
𝒰 ⊔ ℕ = incons
𝒰 ⊔ (F _) = incons
𝒰 ⊔ (refl _) = incons
𝒰 ⊔ (I _ _ _) = incons
𝒰 ⊔ (Π _ _) = incons
𝒰 ⊔ 𝒰 = 𝒰
𝒰 ⊔ incons = incons
incons ⊔ _ = incons

-- The supremum of all first components of a finite function.
pre : FinFun Nbh Nbh → Nbh
pre ∅ = ⊥
pre ((u , v) ∷ f) = u ⊔ pre f

-- The supremum of all second components of a finite function.
post : FinFun Nbh Nbh → Nbh
post ∅ = ⊥
post ((u , v) ∷ f) = v ⊔ post f
