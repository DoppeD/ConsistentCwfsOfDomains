module Cwf.DavidBool where

open import Agda.Builtin.Bool public
open import Agda.Builtin.Equality

_∧_ : Bool → Bool → Bool
false ∧ q = false
true ∧ q = q

infixl 10 _∧_

∧-lemma₁ : ∀ {p q} → p ∧ q ≡ true → p ≡ true
∧-lemma₁ {true} _ = refl
∧-lemma₁ {false} {true} ()
∧-lemma₁ {false} {false} ()

∧-lemma₂ : ∀ {p q} → p ∧ q ≡ true → q ≡ true
∧-lemma₂ {q = true} _ = refl
∧-lemma₂ {true} {false} ()
∧-lemma₂ {false} {false} ()

∧-lemma₃ : ∀ {p q} → p ≡ true → q ≡ true → p ∧ q ≡ true
∧-lemma₃ refl refl = refl

_∨_ : Bool → Bool → Bool
true ∨ q = true
false ∨ q = q

infixl 5 _∨_

not : Bool → Bool
not true = false
not false = true
