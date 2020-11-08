module Cwf.ConProperties where

open import Base.Core using (_,_)
open import Base.FinFun
open import Cwf.UniType

open import Agda.Builtin.Size

-- These show that two neighborhoods are always either consistent or not.
con∨¬con : ∀ {i} → {x y : Nbh i} →
           Con x y ∨ ¬Con x y
cff∨¬cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
           ConFinFun 𝑓 ∨ ¬ConFinFun 𝑓

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

ase : ∀ {i} → {x y x′ y′ x″ y″ : Nbh i} →
      ¬Con x x ∨ Con y y →
      (x′ , y′) ∈ ((x , y) ∷ ∅) →
      (x″ , y″) ∈ ((x , y) ∷ ∅) →
      ¬Con x′ x″ ∨ Con y′ y″
ase proof here here = proof

cff∨¬cff {𝑓 = ∅} = inl (cff xy∈∅-abs)
cff∨¬cff {𝑓 = ((x , y) ∷ ∅)}
  with (con∨¬con {x = x} {x}) | con∨¬con {x = y} {y}
... | inl conxx | inl conyy
  = inl (cff (ase (inr conyy)))
... | inl x₁ | inr x₂ = {!!}
... | inr ¬conxx | _
  = inl (cff (ase (inl ¬conxx)))
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  with (cff∨¬cff {𝑓 = ((x , y) ∷ 𝑓)}) | cff∨¬cff {𝑓 = ((x′ , y′) ∷ 𝑓)}
... | inl x₁ | inl x₂ = {!!}
... | inl x₁ | inr x₂ = {!!}
... | inr x₁ | _ = {!!}

¬con∧¬con : ∀ {i} → {x y : Nbh i} → Con x y →
            ¬Con x y → absurd
¬cff∧¬cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
            ConFinFun 𝑓 → ¬CffProof i 𝑓 → absurd

cff-sym : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
          ConFinFun (𝑓 ∪ 𝑔) → ConFinFun (𝑔 ∪ 𝑓)
cff-sym {𝑓 = 𝑓} (cff p)
  = cff λ xy∈𝑓∪𝑔 x′y′∈𝑓∪𝑔 → p (∪-lemma₈ {𝑓′ = 𝑓} xy∈𝑓∪𝑔)
    (∪-lemma₈ {𝑓′ = 𝑓} x′y′∈𝑓∪𝑔)

-- These show that two neighborhoods can't both be consistent and not consistent.
¬con∧¬con {x = ⊥} conxy (¬con-sym (¬con-sym ¬conxy))
  = ¬con∧¬con conxy ¬conxy
¬con∧¬con {x = 0ₙ} conxy (¬con-sym (¬con-sym ¬conxy))
  = ¬con∧¬con conxy ¬conxy
¬con∧¬con {x = ℕ} conxy (¬con-sym (¬con-sym ¬conxy))
  = ¬con∧¬con conxy ¬conxy
¬con∧¬con {x = λᵤ 𝑓} {y = ⊥}  conxy (¬con-sym (¬con-sym ¬conxy))
  = ¬con∧¬con conxy ¬conxy
¬con∧¬con (con-λ cff∪) (¬con-λ (¬cff ¬cffp))
  = ¬cff∧¬cff cff∪ ¬cffp
¬con∧¬con {x = λᵤ 𝑓} {y = λᵤ 𝑔} (con-λ cff∪) (¬con-sym ¬con𝑔𝑓)
  = ¬con∧¬con (con-λ (cff-sym {𝑓 = 𝑓} cff∪)) ¬con𝑔𝑓

¬cff∧¬cff (cff p)
  record { xy∈𝑓 = xy∈𝑓
         ; x′y′∈𝑓 = x′y′∈𝑓
         ; conxx′ = conxx′
         ; ¬conyy′ = ¬conyy′
         }
  with (p xy∈𝑓 x′y′∈𝑓)
... | inl ¬conxx′ = ¬con∧¬con conxx′ ¬conxx′
... | inr conyy′ = ¬con∧¬con conyy′ ¬conyy′
