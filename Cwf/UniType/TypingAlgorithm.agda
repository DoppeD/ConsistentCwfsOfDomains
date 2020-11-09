module Cwf.TypingAlgorithm where

open import Base.Core hiding (List)
open import Base.FinFun
open import Cwf.DavidBool
open import Cwf.DavidList
open import Cwf.Nbh


enumI' : ∀ {i} → UniNbh i → List (UniNbh i) → List (UniNbh i) →
         List (UniNbh i)
enumI' U ∅ [u′] = ∅
enumI' U (u ∷ us) [u′] = (map (I U u) [u′]) ∪ enumI' U us [u′]
{-
-- Enumerate all tests for I U u u′, given [ U ], [ u ] and [ u′ ].
enumI : ∀ {i} → List (u i) → List (u i) → List (u i) → List (u i)
enumI ∅ [u] [u′] = ∅
enumI (U ∷ Us) [u] [u′] = (enumI' U [u] [u′]) ∪ enumI Us [u] [u′]

enumλ' : ∀ {i} → UniNbh i → UniNbh i → List (Listᵤ i) → List (Listᵤ i)
enumλ' u v ∅ = ∅
enumλ' u v (f ∷ fs) = ((u , v) ∷ f) ∷ enumλ' u v fs

enumλ : ∀ {i} → UniNbh i → List (u i) → List (Listᵤ i) → List (Listᵤ i)
enumλ u ∅ [f] = ∅
enumλ u (v ∷ vs) [f] = enumλ' u v [f] ∪ enumλ u vs [f]

enumΠ : ∀ {i} → UniNbh i → List (Listᵤ i) → List (u (↑ i))
enumΠ u [f] = map (Π u) [f]

-- This generates principal ideals.
-- The function [_]ₗ takes a finite function (u₁ → v₁, u₂ → v₂, ..., uₙ → vₙ)
-- and produces a list of finite functions, each on the form
-- (u₁ → w₁, u₂ → w₂, ..., uₙ → wₙ), where wᵢ ∈ [ vᵢ ].
-- Ideally, we would like to minimize finite functions before calling
-- [_]ₗ. For example, if a finite function maps u → v₁ and u → v₂,
-- and v₁ and v₂ are consistent, then we should replace these two
-- with u → (v₁ ⊔ v₂)
[_] : ∀ {i} → UniNbh i → List (u i)
[_]ₗ : ∀ {i} → Listᵤ i → List (Listᵤ i)
[ ⊥ ] = ⊥ ∷ ∅
[ λᵤ f ] = map λᵤ [ f ]ₗ ∪ (⊥ ∷ ∅)
[ Π u f ] = concat (map (λ u′ → enumΠ u′ [ f ]ₗ) [ u ]) ∪ (⊥ ∷ ∅)
[ 0ᵤ ] = 0ᵤ ∷ (⊥ ∷ ∅)
[ s u ] = map s [ u ] ∪ (⊥ ∷ ∅)
[ N ] = N ∷ (⊥ ∷ ∅)
[ refl u ] = map refl [ u ] ∪ (⊥ ∷ ∅)
[ I U u u′ ] = enumI [ U ] [ u ] [ u′ ] ∪ (⊥ ∷ ∅)
[ 𝔘₀ ] = 𝔘₀ ∷ (⊥ ∷ ∅)

[ ∅ ]ₗ = ∅
[ (u , v) ∷ ∅ ]ₗ = map (λ v → (u , v) ∷ ∅) [ v ]
[ (u , v) ∷ (x ∷ f) ]ₗ = enumλ u [ v ] [ x ∷ f ]ₗ

-- Maybe apply should also return a proof that u′ is consistent with the
-- element that apply returns?
-- Not efficient! Must check that u′ is smaller than u, which amounts
-- to checking (u′ elementOf [ u ]), which will in the worst case
-- check u′ ≈ᵤ u″ for every u″ in the list [ u ].
-- It should be fairly easy to implement _⊑_ : u i → u i → Bool such that
-- u′ ⊑ u is logically equivalent to u′ elementOf [ u ]. Using such
-- a function should be more efficient.
apply' : ∀ {i} → (f : Listᵤ i) → isConsFun f ≡ true → UniNbh i → List (u i) → UniNbh i
apply' ∅ _ _ _ = ⊥
apply' ((u′ , v′) ∷ f) p u [u] with (u′ elementOf [u])
... | false = apply' f (consFunLemma₁ (u′ , v′) f p) u [u]
... | true = sup v′ (apply' f (consFunLemma₁ (u′ , v′) f p) u [u]) {!!}

-- Applying a finite function f to a finite element u results in
-- the supremum of all "seconds" of (uᵢ , vᵢ) that satisfy uᵢ ⊑ u.
-- The latter condition is equivalent to uᵢ ∈ [ u ],
-- so we calculate [ u ] and send as argument to apply',
-- which does the actual calculation.
apply : ∀ {i} → (f : Listᵤ i) → isConsFun f ≡ true → UniNbh i → UniNbh i
apply f p u = apply' f p u [ u ]

-- Testing U Type and u : U are defined mutually.

-- Tests U type.
testUType : ∀ {i} → UniNbh i → Bool

-- Tests u : U.
-- For the specific case of testing whether λᵤ f : Π U F, we
-- need to prove that F is a consistent function in order to
-- apply it.
testu:U : ∀ {i} → UniNbh i → UniNbh i → Bool
testu:U ⊥ U = testUType U
testu:U (λᵤ ∅) (Π U f) = true -- We should also require testUType U?
testu:U (λᵤ ((u , v) ∷ f)) (Π U F)
  = false -- testu:U u U ∧ testu:U v (apply F {!!} u) ∧ testu:U (λᵤ f) (Π U F)
testu:U (λᵤ f) U = false
-- To test whether Π U (u₁ → V₁, u₂ → V₂, ..., uₙ → Vₙ) : 𝔘₀, we first
-- test that V₁ : 𝔘₀ that u₁ : U, then that V₂ : 𝔘₀ and that
-- u₂ : U, and so on. Once the entire finite function is checked
-- in this way, we check that U : 𝔘₀.
testu:U (Π U ∅) 𝔘₀ = testu:U U 𝔘₀
testu:U (Π U ((u , V) ∷ f)) 𝔘₀
  = testu:U u U ∧ testu:U V 𝔘₀ ∧ testu:U (Π U f) 𝔘₀
testu:U (Π U f) U′ = false
testu:U 0ᵤ N = true
testu:U 0ᵤ U = false
testu:U (s u) N = testu:U u N
testu:U (s u) U = false
testu:U N 𝔘₀ = true
testu:U N U = false
testu:U (refl u) (I U u′ u″)
  = testUType U ∧ testu:U u U ∧ u ≈ᵤ u′ ∧ u′ ≈ᵤ u″
testu:U (refl u) U = false
testu:U (I U u u′) 𝔘₀
  = testu:U U 𝔘₀ ∧ testu:U u U ∧ testu:U u′ U
testu:U (I U u u′) U′ = false
testu:U 𝔘₀ U = false

testUType ⊥ = false
testUType (λᵤ f) = false
-- To test whether Π U (u₁ → V₁, u₂ → V₂, ..., uₙ → Vₙ) is a type, we first
-- test that V₁ is a type and that u₁ : U, then that V₂ is a type and
-- that u₂ : U, and so on. Once the entire finite function is checked
-- in this way, we check that U is a type.
testUType (Π U ∅) = testUType U
testUType (Π U ((u , V) ∷ f))
  = testUType V ∧ testu:U u U ∧ testUType (Π U f)
testUType 0ᵤ = false
testUType (s u) = false
testUType N = true
testUType (refl u) = false
-- I U u u′ is a type if U is a type, and both u : U and u′ : U.
testUType (I U u u′)
  = testUType U ∧ testu:U u U ∧ testu:U u′ U
testUType 𝔘₀ = true
-}
