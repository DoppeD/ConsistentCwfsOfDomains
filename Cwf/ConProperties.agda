module Cwf.ConProperties where

open import Base.Core using (_,_)
open import Base.FinFun
open import Cwf.UniType

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

conLemma₁ : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh i) (Nbh i)} →
            𝑓 ⊆ 𝑓′ → ¬ConFinFun 𝑓 → ¬ConFinFun 𝑓′
conLemma₁ 𝑓⊆𝑓′
  (¬cff record
          { x = x
          ; y = y
          ; x′ = x′
          ; y′ = y′ ; xy∈𝑓 = xy∈𝑓
          ; x′y′∈𝑓 = x′y′∈𝑓
          ; conxx′ = conxx′
          ; ¬conyy′ = ¬conyy′ }
          )
  = ¬cff (record
            { x = x
            ; y = y
            ; x′ = x′
            ; y′ = y′
            ; xy∈𝑓 = 𝑓⊆𝑓′ xy∈𝑓
            ; x′y′∈𝑓 = 𝑓⊆𝑓′ x′y′∈𝑓
            ; conxx′ = conxx′
            ; ¬conyy′ = ¬conyy′
            })

cffSym : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
         ConFinFun (𝑓 ∪ 𝑔) → ConFinFun (𝑔 ∪ 𝑓)
cffSym {𝑓 = 𝑓} (cff p)
  = cff λ xy∈𝑓∪𝑔 x′y′∈𝑓∪𝑔 → p (∪-lemma₈ {𝑓′ = 𝑓} xy∈𝑓∪𝑔)
    (∪-lemma₈ {𝑓′ = 𝑓} x′y′∈𝑓∪𝑔)

conSym : ∀ {i} → {x y : Nbh i} → Con x y → Con y x
conSym con-⊥₁ = con-⊥₂
conSym con-⊥₂ = con-⊥₁
conSym con-refl-0 = con-refl-0
conSym (con-s consxsy) = con-s (conSym consxsy)
conSym con-refl-ℕ = con-refl-ℕ
conSym con-refl-𝒰 = con-refl-𝒰
conSym (con-Π {𝑓 = 𝑓} conxy cff𝑓∪𝑔)
  = con-Π (conSym conxy) (cffSym {𝑓 = 𝑓} cff𝑓∪𝑔)
conSym (con-λ {𝑓 = 𝑓} cff∪) = con-λ (cffSym {𝑓 = 𝑓} cff∪)

¬cffSym : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
          ¬ConFinFun (𝑓 ∪ 𝑔) → ¬ConFinFun (𝑔 ∪ 𝑓)
¬cffSym {𝑓 = 𝑓}
  (¬cff record
          { x = x
          ; y = y
          ; x′ = x′
          ; y′ = y′
          ; xy∈𝑓 = xy∈𝑓
          ; x′y′∈𝑓 = x′y′∈𝑓
          ; conxx′ = conxx′
          ; ¬conyy′ = ¬conyy′
          })
  = ¬cff (record
            { x = x
            ; y = y
            ; x′ = x′
            ; y′ = y′
            ; xy∈𝑓 = ∪-lemma₈ {𝑓 = 𝑓} xy∈𝑓
            ; x′y′∈𝑓 = ∪-lemma₈ {𝑓 = 𝑓} x′y′∈𝑓
            ; conxx′ = conxx′
            ; ¬conyy′ = ¬conyy′
            })

sameBranchSym : ∀ {i} → {x y : Nbh i} → sameBranch x y ≡ false → sameBranch y x ≡ false
sameBranchSym {x = ⊥} ()
sameBranchSym {x = 0ₙ} {y = ⊥} ()
sameBranchSym {x = 0ₙ} {y = 0ₙ} ()
sameBranchSym {x = 0ₙ} {y = sᵤ y} _ = refl
sameBranchSym {x = 0ₙ} {y = ℕ} _ = refl
sameBranchSym {x = 0ₙ} {y = 𝒰} _ = refl
sameBranchSym {x = 0ₙ} {y = λᵤ _} _ = refl
sameBranchSym {x = 0ₙ} {y = Π _ _} _ = refl
sameBranchSym {x = sᵤ _} {y = ⊥} ()
sameBranchSym {x = sᵤ _} {y = 0ₙ} _ = refl
sameBranchSym {x = sᵤ _} {y = sᵤ _} ()
sameBranchSym {x = sᵤ _} {y = ℕ} _ = refl
sameBranchSym {x = sᵤ _} {y = 𝒰} _ = refl
sameBranchSym {x = sᵤ _} {y = λᵤ _} _ = refl
sameBranchSym {x = sᵤ _} {y = Π _ _} _ = refl
sameBranchSym {x = ℕ} {y = ⊥} ()
sameBranchSym {x = ℕ} {y = 0ₙ} _ = refl
sameBranchSym {x = ℕ} {y = sᵤ _} _ = refl
sameBranchSym {x = ℕ} {y = ℕ} ()
sameBranchSym {x = ℕ} {y = 𝒰} _ = refl
sameBranchSym {x = ℕ} {y = λᵤ _} _ = refl
sameBranchSym {x = ℕ} {y = Π _ _} _ = refl
sameBranchSym {x = 𝒰} {y = ⊥} ()
sameBranchSym {x = 𝒰} {y = 0ₙ} _ = refl
sameBranchSym {x = 𝒰} {y = sᵤ _} _ = refl
sameBranchSym {x = 𝒰} {y = ℕ} _ = refl
sameBranchSym {x = 𝒰} {y = 𝒰} ()
sameBranchSym {x = 𝒰} {y = λᵤ _} _ = refl
sameBranchSym {x = 𝒰} {y = Π _ _} _ = refl
sameBranchSym {x = λᵤ _} {y = ⊥} ()
sameBranchSym {x = λᵤ _} {y = 0ₙ} _ = refl
sameBranchSym {x = λᵤ _} {y = sᵤ _} _ = refl
sameBranchSym {x = λᵤ _} {y = ℕ} _ = refl
sameBranchSym {x = λᵤ _} {y = 𝒰} _ = refl
sameBranchSym {x = λᵤ _} {y = λᵤ _} ()
sameBranchSym {x = λᵤ _} {y = Π _ _} _ = refl
sameBranchSym {x = Π _ _} {y = ⊥} ()
sameBranchSym {x = Π _ _} {y = 0ₙ} _ = refl
sameBranchSym {x = Π _ _} {y = sᵤ _} _ = refl
sameBranchSym {x = Π _ _} {y = ℕ} _ = refl
sameBranchSym {x = Π _ _} {y = 𝒰} _ = refl
sameBranchSym {x = Π _ _} {y = λᵤ _} _ = refl
sameBranchSym {x = Π _ _} {y = Π _ _} ()

¬conSym : ∀ {i} → {x y : Nbh i} → ¬Con x y → ¬Con y x
¬conSym (¬con-s ¬conxy) = ¬con-s (¬conSym ¬conxy)
¬conSym (¬con-λ {𝑓 = 𝑓} ¬cff𝑓∪𝑔) = ¬con-λ (¬cffSym {𝑓 = 𝑓} ¬cff𝑓∪𝑔)
¬conSym (¬con-Π₁ ¬conxy) = ¬con-Π₁ (¬conSym ¬conxy)
¬conSym (¬con-Π₂ {𝑓 = 𝑓} ¬cff𝑓∪𝑔) = ¬con-Π₂ (¬cffSym {𝑓 = 𝑓} ¬cff𝑓∪𝑔)
¬conSym (¬con-br ¬sb) = ¬con-br (sameBranchSym ¬sb)

cff∨¬cff'' : ∀ {i} → {x y x′ y′ x″ y″ : Nbh i} →
            ¬Con x x ∨ Con y y →
            (x′ , y′) ∈ ((x , y) ∷ ∅) →
            (x″ , y″) ∈ ((x , y) ∷ ∅) →
            ¬Con x′ x″ ∨ Con y′ y″
cff∨¬cff'' proof here here = proof

cff∨¬cff' : ∀ {i} → {x y x′ y′ : Nbh i} →
            {𝑓 : FinFun (Nbh i) (Nbh i)} →
            ¬Con x x′ ∨ Con y y′ →
            ConFinFun ((x , y) ∷ 𝑓) →
            ConFinFun ((x′ , y′) ∷ 𝑓) →
            {u v u′ v′ : Nbh i} →
            (u , v) ∈ ((x , y) ∷ ((x′ , y′) ∷ 𝑓)) →
            (u′ , v′) ∈ ((x , y) ∷ ((x′ , y′) ∷ 𝑓)) →
            ¬Con u u′ ∨ Con v v′
cff∨¬cff' _ (cff proof) _ here here
  = proof here here
cff∨¬cff' _ (cff _) (cff proof) (there here) (there here)
  = proof here here
cff∨¬cff' p₁ (cff _) (cff _) here (there here)
  = p₁
cff∨¬cff' (inl ¬conxx′) (cff _) (cff _) (there here) here
  = inl (¬conSym ¬conxx′)
cff∨¬cff' (inr conyy′) (cff _) (cff _) (there here) here
  = inr (conSym conyy′)
cff∨¬cff' _ (cff proof) (cff _) here (there (there u′v′∈𝑓))
  = proof here (there u′v′∈𝑓)
cff∨¬cff' _ (cff proof) (cff _) (there (there uv∈𝑓)) here
  = proof (there uv∈𝑓) here
cff∨¬cff' _ (cff _) (cff proof) (there here) (there (there u′v′∈𝑓))
  = proof here (there u′v′∈𝑓)
cff∨¬cff' _ (cff _) (cff proof) (there (there uv∈𝑓)) (there here)
  = proof (there uv∈𝑓) here
cff∨¬cff' _ (cff _) (cff proof) (there (there uv∈𝑓)) (there (there u′v′∈𝑓))
  = proof (there uv∈𝑓) (there u′v′∈𝑓)

-- These show that two neighborhoods are always either consistent or not.
con∨¬con : ∀ {i} → {x y : Nbh i} →
           Con x y ∨ ¬Con x y
cff∨¬cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
           ConFinFun 𝑓 ∨ ¬ConFinFun 𝑓

con∨¬con {x = ⊥} {_} = inl con-⊥₁
con∨¬con {x = 0ₙ} {⊥} = inl con-⊥₂
con∨¬con {x = 0ₙ} {0ₙ} = inl con-refl-0
con∨¬con {x = 0ₙ} {sᵤ _} = inr (¬con-br refl)
con∨¬con {x = 0ₙ} {ℕ} = inr (¬con-br refl)
con∨¬con {x = 0ₙ} {𝒰} = inr (¬con-br refl)
con∨¬con {x = 0ₙ} {λᵤ _} = inr (¬con-br refl)
con∨¬con {x = 0ₙ} {Π _ _} = inr (¬con-br refl)
con∨¬con {x = sᵤ _} {⊥} = inl con-⊥₂
con∨¬con {x = sᵤ _} {0ₙ} = inr (¬con-br refl)
con∨¬con {x = sᵤ x} {sᵤ y}
  with (con∨¬con {x = x} {y})
... | inl conxy = inl (con-s conxy)
... | inr ¬conxy = inr (¬con-s ¬conxy)
con∨¬con {x = sᵤ _} {ℕ} = inr (¬con-br refl)
con∨¬con {x = sᵤ _} {𝒰} = inr (¬con-br refl)
con∨¬con {x = sᵤ _} {λᵤ _} = inr (¬con-br refl)
con∨¬con {x = sᵤ _} {Π _ 𝑔} = inr (¬con-br refl)
con∨¬con {x = ℕ} {⊥} = inl con-⊥₂
con∨¬con {x = ℕ} {0ₙ} = inr (¬con-br refl)
con∨¬con {x = ℕ} {sᵤ _} = inr (¬con-br refl)
con∨¬con {x = ℕ} {ℕ} = inl con-refl-ℕ
con∨¬con {x = ℕ} {𝒰} = inr (¬con-br refl)
con∨¬con {x = ℕ} {λᵤ _} = inr (¬con-br refl)
con∨¬con {x = ℕ} {Π _ _} = inr (¬con-br refl)
con∨¬con {x = 𝒰} {⊥} = inl con-⊥₂
con∨¬con {x = 𝒰} {0ₙ} = inr (¬con-br refl)
con∨¬con {x = 𝒰} {sᵤ _} = inr (¬con-br refl)
con∨¬con {x = 𝒰} {ℕ} = inr (¬con-br refl)
con∨¬con {x = 𝒰} {λᵤ _} = inr (¬con-br refl)
con∨¬con {x = 𝒰} {𝒰} = inl con-refl-𝒰
con∨¬con {x = 𝒰} {Π _ _} = inr (¬con-br refl)
con∨¬con {x = λᵤ _} {⊥} = inl con-⊥₂
con∨¬con {x = λᵤ _} {0ₙ} = inr (¬con-br refl)
con∨¬con {x = λᵤ _} {sᵤ _} = inr (¬con-br refl)
con∨¬con {x = λᵤ _} {ℕ} = inr (¬con-br refl)
con∨¬con {x = λᵤ _} {𝒰} = inr (¬con-br refl)
con∨¬con {x = λᵤ 𝑓} {λᵤ 𝑔} with (cff∨¬cff {𝑓 = 𝑓 ∪ 𝑔})
... | inl cff∪ = inl (con-λ cff∪)
... | inr ¬cff∪ = inr (¬con-λ ¬cff∪)
con∨¬con {x = λᵤ 𝑓} {Π _ _} = inr (¬con-br refl)
con∨¬con {x = Π x 𝑓} {⊥} = inl con-⊥₂
con∨¬con {x = Π x 𝑓} {0ₙ} = inr (¬con-br refl)
con∨¬con {x = Π x 𝑓} {sᵤ y} = inr (¬con-br refl)
con∨¬con {x = Π x 𝑓} {ℕ} = inr (¬con-br refl)
con∨¬con {x = Π x 𝑓} {𝒰} = inr (¬con-br refl)
con∨¬con {x = Π x 𝑓} {λᵤ y} = inr (¬con-br refl)
con∨¬con {x = Π x 𝑓} {Π y 𝑔}
  with (con∨¬con {x = x} {y}) | cff∨¬cff {𝑓 = 𝑓 ∪ 𝑔}
... | inr ¬conxy | _ = inr (¬con-Π₁ ¬conxy)
... | inl _ | inr ¬cff𝑓∪𝑔 = inr (¬con-Π₂ ¬cff𝑓∪𝑔)
... | inl conxy | inl cff𝑓∪𝑔 = inl (con-Π conxy cff𝑓∪𝑔)

cff∨¬cff {𝑓 = ∅} = inl (cff xy∈∅-abs)
cff∨¬cff {𝑓 = ((x , y) ∷ ∅)}
  with (con∨¬con {x = x} {x}) | con∨¬con {x = y} {y}
cff∨¬cff {𝑓 = ((x , y) ∷ ∅)} | inl conxx | inl conyy
  = inl (cff (cff∨¬cff'' (inr conyy)))
cff∨¬cff {𝑓 = ((x , y) ∷ ∅)} | inl conxx | inr ¬conyy
  = inr (¬cff (record
                 { x = x
                 ; y = y
                 ; x′ = x
                 ; y′ = y
                 ; xy∈𝑓 = here
                 ; x′y′∈𝑓 = here
                 ; conxx′ = conxx
                 ; ¬conyy′ = ¬conyy
                 }))
cff∨¬cff {𝑓 = ((x , y) ∷ ∅)} | inr ¬conxx | _
  = inl (cff (cff∨¬cff'' (inl ¬conxx)))
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  with (cff∨¬cff {𝑓 = ((x , y) ∷ 𝑓)}) | cff∨¬cff {𝑓 = ((x′ , y′) ∷ 𝑓)}
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  | inl cffxy𝑓 | inl cffx′y′𝑓
  with (con∨¬con {x = x} {x′}) | con∨¬con {x = y} {y′}
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  | inl cffxy𝑓 | inl cffx′y′𝑓 | inl _ | inl conyy′
  = inl (cff (cff∨¬cff' (inr conyy′) cffxy𝑓 cffx′y′𝑓))
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  | inl cffxy𝑓 | inl cffx′y′𝑓 | inl conxx′ | inr ¬conyy′
  = inr (¬cff (record
                 { x = x
                 ; y = y
                 ; x′ = x′
                 ; y′ = y′
                 ; xy∈𝑓 = here
                 ; x′y′∈𝑓 = there here
                 ; conxx′ = conxx′
                 ; ¬conyy′ = ¬conyy′
                 }))
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  | inl cffxy𝑓 | inl cffx′y′𝑓 | inr ¬conxx′ | _
  = inl (cff (cff∨¬cff' (inl ¬conxx′) cffxy𝑓 cffx′y′𝑓))
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  | inl cffxy𝑓 | inr ¬cffx′y′𝑓
  = inr (conLemma₁ ⊆-lemma₃ ¬cffx′y′𝑓)
cff∨¬cff {𝑓 = ((x , y) ∷ ((x′ , y′) ∷ 𝑓))}
  | inr ¬cffxy𝑓 | _
  = inr (conLemma₁ (⊆-lemma₄ here (⊆-lemma₂ ⊆-lemma₃)) ¬cffxy𝑓)

¬con∧¬con' : ∀ {i} → {x : Nbh i} → ¬Con x ⊥ → absurd
¬con∧¬con' {x = ⊥} (¬con-br ())
¬con∧¬con' {x = 0ₙ} (¬con-br ())
¬con∧¬con' {x = sᵤ x} (¬con-br ())
¬con∧¬con' {x = ℕ} (¬con-br ())
¬con∧¬con' {x = 𝒰} (¬con-br ())
¬con∧¬con' {x = λᵤ x} (¬con-br ())
¬con∧¬con' {x = Π x x₁} (¬con-br ())

-- These show that two neighborhoods can't both be consistent and not consistent.
¬con∧¬con : ∀ {i} → {x y : Nbh i} → Con x y →
            ¬Con x y → absurd
¬cff∧¬cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
            ConFinFun 𝑓 → ¬CffProof i 𝑓 → absurd

¬con∧¬con (con-s conxy) (¬con-s ¬conxy)
  = ¬con∧¬con conxy ¬conxy
¬con∧¬con (con-Π conxy _) (¬con-Π₁ ¬conxy)
  = ¬con∧¬con conxy ¬conxy
¬con∧¬con (con-Π _ cff𝑓∪𝑔) (¬con-Π₂ (¬cff ¬cffp))
  = ¬cff∧¬cff cff𝑓∪𝑔 ¬cffp
¬con∧¬con (con-λ cff∪) (¬con-λ (¬cff ¬cffp))
  = ¬cff∧¬cff cff∪ ¬cffp
¬con∧¬con {x = x} con-⊥₁ (¬con-br ¬sb⊥y)
  = ¬con∧¬con' {x = x} (¬conSym (¬con-br ¬sb⊥y))
¬con∧¬con con-⊥₂ (¬con-br ¬sbx⊥)
  = ¬con∧¬con' (¬con-br ¬sbx⊥)

¬cff∧¬cff (cff p)
  record { xy∈𝑓 = xy∈𝑓
         ; x′y′∈𝑓 = x′y′∈𝑓
         ; conxx′ = conxx′
         ; ¬conyy′ = ¬conyy′
         }
  with (p xy∈𝑓 x′y′∈𝑓)
... | inl ¬conxx′ = ¬con∧¬con conxx′ ¬conxx′
... | inr conyy′ = ¬con∧¬con conyy′ ¬conyy′
