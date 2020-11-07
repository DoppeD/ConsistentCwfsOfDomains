module Cwf.test where

open import Base.Core using (_,_)
open import Base.FinFun

open import Agda.Builtin.Size

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A B : Set) : Set where
  ∧-intro : A → B → A ∧ B

data absurd : Set where

data Nbh : Size → Set where
  ⊥ : ∀ {i} → Nbh i
  0ₙ : ∀ {i} → Nbh i
  ℕ : ∀ {i} → Nbh i
  λᵤ : ∀ {i} → (𝑓 : FinFun (Nbh i) (Nbh i)) → Nbh (↑ i)

data Con : ∀ {i} → Nbh i → Nbh i → Set
data ConFinFun : ∀ {i} → FinFun (Nbh i) (Nbh i) → Set
data ¬Con : ∀ {i} → Nbh i → Nbh i → Set
data ¬ConFinFun : ∀ {i} → FinFun (Nbh i) (Nbh i) → Set
-- This is a record that proves that there exist pairs (x , y) ∈ 𝑓 and
-- (x′ , y′) ∈ 𝑓 such that x and x′ are consistent but y and y′ are not.
record Thing (i : Size) (𝑓 : FinFun (Nbh i) (Nbh i)) : Set

data Con where
  con-⊥₁ : ∀ {i} → {x : Nbh i} → Con ⊥ x
  con-⊥₂ : ∀ {i} → {x : Nbh i} → Con x ⊥
  con-refl-0 : ∀ {i} → Con (0ₙ {i}) 0ₙ
  con-refl-ℕ : ∀ {i} → Con (ℕ {i}) ℕ
  con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} → ConFinFun (𝑓 ∪ 𝑔) →
          Con (λᵤ 𝑓) (λᵤ 𝑔)

data ConFinFun where
  cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
        ({x y x′ y′ : Nbh i} → (x , y) ∈ 𝑓 → (x′ , y′) ∈ 𝑓 → ¬Con x x′ ∨ Con y y′) →
        ConFinFun 𝑓
         
data ¬Con where
  ¬con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} → ¬ConFinFun (𝑓 ∪ 𝑔) → ¬Con (λᵤ 𝑓) (λᵤ 𝑔)
  ¬con-sym : ∀ {i} → {x y : Nbh i} → ¬Con x y → ¬Con y x
  ¬con-0λ : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ¬Con 0ₙ (λᵤ 𝑓)
  ¬con-0ℕ : ∀ {i} → ¬Con (0ₙ {i}) ℕ
  ¬con-ℕλ : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ¬Con ℕ (λᵤ 𝑓)

record Thing i 𝑓 where
  inductive
  field
    x y x′ y′ : Nbh i
    xy∈𝑓 : (x , y) ∈ 𝑓
    x′y′∈𝑓 : (x′ , y′) ∈ 𝑓
    conxx′ : Con x x′
    ¬conyy′ : ¬Con y y′

data ¬ConFinFun where
  ¬cff : ∀ {i 𝑓} → Thing i 𝑓 → ¬ConFinFun 𝑓

---- EVERYTHING BELOW IN SEPARATE MODULE ----

-- These show that two neighborhoods are always either consistent or not.
con∨¬con : ∀ {i} → {x y : Nbh i} → Con x y ∨ ¬Con x y
cff∨¬cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ConFinFun 𝑓 ∨ ¬ConFinFun 𝑓

con∨¬con {x = ⊥} {y} = inl con-⊥₁
con∨¬con {x = 0ₙ} {⊥} = inl con-⊥₂
con∨¬con {x = 0ₙ} {0ₙ} = inl con-refl-0
con∨¬con {x = 0ₙ} {ℕ} = inr ¬con-0ℕ
con∨¬con {x = 0ₙ} {λᵤ 𝑓} = inr ¬con-0λ
con∨¬con {x = ℕ} {⊥} = inl con-⊥₂
con∨¬con {x = ℕ} {0ₙ} = inr (¬con-sym ¬con-0ℕ)
con∨¬con {x = ℕ} {ℕ} = inl con-refl-ℕ
con∨¬con {x = ℕ} {λᵤ 𝑓} = inr ¬con-ℕλ
con∨¬con {x = λᵤ 𝑓} {⊥} = inl con-⊥₂
con∨¬con {x = λᵤ 𝑓} {0ₙ} = inr (¬con-sym ¬con-0λ)
con∨¬con {x = λᵤ 𝑓} {ℕ} = inr (¬con-sym ¬con-ℕλ)
con∨¬con {x = λᵤ 𝑓} {λᵤ 𝑔} with (cff∨¬cff {𝑓 = 𝑓 ∪ 𝑔})
... | inl cff∪ = inl (con-λ cff∪)
... | inr ¬cff∪ = inr (¬con-λ ¬cff∪)

cff∨¬cff {𝑓 = ∅} = inl (cff xy∈∅-abs)
cff∨¬cff {𝑓 = ((x , y) ∷ 𝑓)} = {!!}

biff : ∀ {i} → {x : Nbh i} → ¬Con x ⊥ → absurd
biff (¬con-sym (¬con-sym x)) = biff x

¬con∧¬con : ∀ {i} → {x y : Nbh i} → Con x y → ¬Con x y → absurd
¬cff∧¬cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ConFinFun 𝑓 → Thing i 𝑓 → absurd

cff-sym : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} → ConFinFun (𝑓 ∪ 𝑔) → ConFinFun (𝑔 ∪ 𝑓)
cff-sym {𝑓 = 𝑓} (cff p)
  = cff λ xy∈𝑓∪𝑔 x′y′∈𝑓∪𝑔 → p (∪-lemma₈ {𝑓′ = 𝑓} xy∈𝑓∪𝑔)
    (∪-lemma₈ {𝑓′ = 𝑓} x′y′∈𝑓∪𝑔)

-- These show that two neighborhoods can't both be consistent and not consistent.
¬con∧¬con {x = ⊥} {⊥} a (¬con-sym b) = ¬con∧¬con a b
¬con∧¬con {x = ⊥} {0ₙ} a (¬con-sym b) = biff b
¬con∧¬con {x = ⊥} {ℕ} a (¬con-sym b) = biff b
¬con∧¬con {x = ⊥} {λᵤ 𝑓} a (¬con-sym b) = biff b
¬con∧¬con {x = 0ₙ} {⊥} a (¬con-sym (¬con-sym b)) = biff b
¬con∧¬con {x = 0ₙ} {0ₙ} a (¬con-sym b) = ¬con∧¬con a b
¬con∧¬con {x = ℕ} {⊥} a b = biff b
¬con∧¬con {x = ℕ} {ℕ} a (¬con-sym b) = ¬con∧¬con a b
¬con∧¬con {x = λᵤ 𝑓} {⊥} a b = biff b
¬con∧¬con {x = λᵤ 𝑓} {λᵤ 𝑔} (con-λ cff∪) (¬con-λ (¬cff x)) = ¬cff∧¬cff cff∪ x
¬con∧¬con {x = λᵤ 𝑓} {λᵤ 𝑔} (con-λ cff∪) (¬con-sym b)
  = ¬con∧¬con {x = λᵤ 𝑔} {λᵤ 𝑓} (con-λ (cff-sym {𝑓 = 𝑓} cff∪)) b 

¬cff∧¬cff (cff p)
  record { xy∈𝑓 = xy∈𝑓
         ; x′y′∈𝑓 = x′y′∈𝑓
         ; conxx′ = conxx′
         ; ¬conyy′ = ¬conyy′
         }
  with (p xy∈𝑓 x′y′∈𝑓)
... | inl ¬conxx′ = ¬con∧¬con conxx′ ¬conxx′
... | inr conyy′ = ¬con∧¬con conyy′ ¬conyy′
