module Cwf.test where

open import Base.Core using (_,_)
open import Base.FinFun

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A B : Set) : Set where
  ∧-intro : A → B → A ∧ B

data Nbh : Set where
  ⊥ : Nbh
  0ₙ : Nbh
  ℕ : Nbh
  λᵤ : (𝑓 : FinFun Nbh Nbh) → Nbh

data Con : Nbh → Nbh → Set
data ConFinFun : FinFun Nbh Nbh → Set
data ¬Con : Nbh → Nbh → Set
data ¬ConFinFun : FinFun Nbh Nbh → Set
record Thing (𝑓 : FinFun Nbh Nbh) : Set

data Con where
  con-⊥₁ : ∀ {x} → Con ⊥ x
  con-⊥₂ : ∀ {x} → Con x ⊥
  con-refl : ∀ {x} → Con x x
  con-λ : ∀ {𝑓 𝑔} → ConFinFun (𝑓 ∪ 𝑔) → Con (λᵤ 𝑓) (λᵤ 𝑔)

data ConFinFun where
  cff₁ : ConFinFun ∅
  cff₂ : ∀ {x y} → ConFinFun ((x , y) ∷ ∅)
  cff₃ : ∀ {x y x′ y′ 𝑓} →
         ¬Con x x′ ∨ (Con y y′ ∧ (ConFinFun ((x , y) ∷ 𝑓) ∧ ConFinFun ((x′ , y′) ∷ 𝑓))) →
         ConFinFun ((x , y) ∷ ((x′ , y′) ∷ 𝑓))

data ¬Con where
  ¬con-λ : ∀ {𝑓 𝑔} → ¬ConFinFun (𝑓 ∪ 𝑔) → ¬Con (λᵤ 𝑓) (λᵤ 𝑔)
  ¬con-sym : ∀ {x y} → ¬Con x y → ¬Con y x
  ¬con-0λ : ∀ {𝑓} → ¬Con 0ₙ (λᵤ 𝑓)
  ¬con-0ℕ : ¬Con 0ₙ ℕ
  ¬con-ℕλ : ∀ {𝑓} → ¬Con ℕ (λᵤ 𝑓)

record Thing 𝑓 where
  inductive
  field
    x y x′ y′ : Nbh
    xy∈𝑓 : (x , y) ∈ 𝑓
    x′y′∈𝑓 : (x′ , y′) ∈ 𝑓
    abs : Con x x′ ∧ ¬Con y y′

data ¬ConFinFun where
  d : ∀ {𝑓} → Thing 𝑓 → ¬ConFinFun 𝑓

-- Maybe have Con as a predicate to Bool and ConFinFun as a data type, and remove ¬Con?

aff : ∀ {x y} → Con x y ∨ ¬Con x y
laff : ∀ {𝑓} → ConFinFun 𝑓 ∨ ¬ConFinFun 𝑓

aff {⊥} {y} = inl con-⊥₁
aff {0ₙ} {⊥} = inl con-⊥₂
aff {0ₙ} {0ₙ} = inl con-refl
aff {0ₙ} {ℕ} = inr ¬con-0ℕ
aff {0ₙ} {λᵤ 𝑓} = inr ¬con-0λ
aff {ℕ} {⊥} = inl con-⊥₂
aff {ℕ} {0ₙ} = inr (¬con-sym ¬con-0ℕ)
aff {ℕ} {ℕ} = inl con-refl
aff {ℕ} {λᵤ 𝑓} = inr ¬con-ℕλ
aff {λᵤ 𝑓} {⊥} = inl con-⊥₂
aff {λᵤ 𝑓} {0ₙ} = inr (¬con-sym ¬con-0λ)
aff {λᵤ 𝑓} {ℕ} = inr (¬con-sym ¬con-ℕλ)
aff {λᵤ 𝑓} {λᵤ 𝑔} with (laff {𝑓 ∪ 𝑔})
... | inl cff∪ = inl (con-λ cff∪)
... | inr ¬cff∪ = inr (¬con-λ ¬cff∪)

laff = {!!}

data absurd : Set where

biff : ∀ {x} → ¬Con x ⊥ → absurd
biff (¬con-sym (¬con-sym x)) = biff x

boff : ∀ {x} → ¬Con x x → absurd
boff (¬con-λ x) = {!!}
boff (¬con-sym x) = boff x

baff : ∀ {x y} → Con x y → ¬Con x y → absurd
baff {⊥} {⊥} a b = boff b
baff {⊥} {0ₙ} a (¬con-sym b) = biff b
baff {⊥} {ℕ} a (¬con-sym b) = biff b
baff {⊥} {λᵤ 𝑓} a (¬con-sym b) = biff b
baff {0ₙ} {⊥} a (¬con-sym (¬con-sym b)) = biff b
baff {0ₙ} {0ₙ} a b = boff b
baff {ℕ} {⊥} a b = biff b
baff {ℕ} {ℕ} a b = boff b
baff {λᵤ 𝑓} {⊥} a b = biff b
baff {λᵤ 𝑓} {λᵤ 𝑔} a b = {!!}
