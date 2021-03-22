{-# OPTIONS --safe #-}

module Base.Core where

open import NbhSys.Definition

open import Agda.Builtin.Nat

private
  variable
    A : Set₁
    n : Nat

-- Standard implementation of a list.
data List : Nat → Set₁ → Set₁ where
  [] : List 0 A
  _::_ : A → List n A → List (suc n) A

-- Notation for lists with one element.
[_] : A → List 1 A
[ x ] = x :: []

head : List (suc n) A → A
head (x :: _) = x

tail : List (suc n) A → List n A
tail (_ :: xs) = xs

-- Standard implementation of a tuple.
-- We reserve the symbol × for other definitions.
data _⊠_ (A B : Set) : Set where
  _,_ : A → B → A ⊠ B

⊠-fst : {A B : Set} → A ⊠ B → A
⊠-fst (a , _) = a

⊠-snd : {A B : Set} → A ⊠ B → B
⊠-snd (_ , b) = b

-- Logical and.
data _∧_ (A B : Set) : Set where
  ∧-intro : A → B → A ∧ B

-- Logical or.
data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data 𝟘 : Set where

¬ : Set → Set
¬ P = P → 𝟘

data 𝟙 : Set where
  * : 𝟙

-- Types are neighborhood systems.
Ty : Set₁
Ty = NbhSys

-- A context is a list of types.
Ctx : Nat → Set₁
Ctx n = List n Ty

-- The below code is adapted from the standard library.
-- The point is to remove any dependencies on libraries.
-- For the purpose of the project, universe levels can be fixed.

Rel : (A : Set₁) → Set₂
Rel A = A → A → Set₁

Reflexive : Rel A → Set₁
Reflexive _≈_ = ∀ {x} → x ≈ x

Symmetric : Rel A → Set₁
Symmetric _≈_ = ∀ {x y} → x ≈ y → y ≈ x

Transitive : Rel A → Set₁
Transitive _≈_ = ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

record IsEquivalence (_≈_ : Rel A) : Set₁ where
  field
    refl : Reflexive _≈_
    sym : Symmetric _≈_
    trans : Transitive _≈_
