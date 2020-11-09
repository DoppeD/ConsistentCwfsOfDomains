module Cwf.DavidList where

open import Agda.Builtin.Nat

data List (A : Set) : Set where
  ∅ : List A
  _∷_ : A → List A → List A

_∪_ : ∀ {A} → List A → List A → List A
(u ∷ 𝑓) ∪ 𝑓′ = u ∷ (𝑓 ∪ 𝑓′)
∅ ∪ 𝑓′ = 𝑓′

concat : ∀ {A} → List (List A) → List A
concat ∅ = ∅
concat (f ∷ fs) = f ∪ concat fs

data _∈_ {A : Set} : A → List A → Set where
  here : ∀ {x fs} → x ∈ (x ∷ fs)
  there : ∀ {x y fs} → x ∈ fs → x ∈ (y ∷ fs)

map : ∀ {A B} → (A → B) → List A → List B
map f ∅ = ∅
map f (x ∷ xs) = f x ∷ map f xs
