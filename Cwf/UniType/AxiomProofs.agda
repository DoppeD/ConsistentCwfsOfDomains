module Cwf.UniType.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition
open import Cwf.UniType.Relation

botElimRight : ∀ {u} → con u → (u ⊔ ⊥) ⊑ u
botElimRight {⊥} conu = ⊑-refl conu
botElimRight {0ᵤ} conu = ⊑-refl conu
botElimRight {s _} conu = ⊑-refl conu
botElimRight {ℕ} conu = ⊑-refl conu
botElimRight {F _} conu = ⊑-refl conu
botElimRight {Π _ _} conu = ⊑-refl conu
botElimRight {𝒰} conu = ⊑-refl conu

botIntroRight : ∀ {u} → con u → u ⊑ (u ⊔ ⊥)
botIntroRight {⊥} conu = ⊑-refl conu
botIntroRight {0ᵤ} conu = ⊑-refl conu
botIntroRight {s u} conu = ⊑-refl conu
botIntroRight {ℕ} conu = ⊑-refl conu
botIntroRight {F x} conu = ⊑-refl conu
botIntroRight {Π u x} conu = ⊑-refl conu
botIntroRight {𝒰} conu = ⊑-refl conu

⊑-refl' : ∀ {u} → con u → u ⊑ u
⊑-refl' conu = ⊑-refl conu

⊑-⊥' : ∀ {u} → con u → ⊥ ⊑ u
⊑-⊥' conu = ⊑-⊥ conu

⊑-⊔-fst' : ∀ {f g u v} → conFinFun (f ∪ g) → (u , v) ∈ f → ⊑-proof (f ∪ g) u v
⊑-⊔-fst' {u = u} {v} (conPairsfg , conElemsfg) uv∈f
  with (conElemsfg {u} (∪-lemma₃ uv∈f))
... | (conu , conv)
  = record { sub = (u , v) ∷ ∅
           ; preable = conAssoc' {u} conu
           ; sub⊆g = ⊆-trans (⊆-lemma₅ uv∈f) ∪-lemma₃
           ; pre⊑u = botElimRight conu
           ; v⊑post = botIntroRight conv
           }

⊑-⊔-fst : ∀ {u v} → con (u ⊔ v) → u ⊑ (u ⊔ v)
⊑-⊔-fst {⊥} conuv = ⊑-⊥ conuv
⊑-⊔-fst {0ᵤ} {⊥} _ = ⊑-refl *
⊑-⊔-fst {0ᵤ} {0ᵤ} _ = ⊑-refl *
⊑-⊔-fst {s _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {s _} {s _} conuv = ⊑-s (⊑-⊔-fst conuv)
⊑-⊔-fst {ℕ} {⊥} _ = ⊑-refl *
⊑-⊔-fst {ℕ} {ℕ} _ = ⊑-refl *
⊑-⊔-fst {F _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {F _} {F _} conuv =
  ⊑-F (subsetIsCon ∪-lemma₃ conuv) conuv (⊑-⊔-fst' conuv)
⊑-⊔-fst {Π _ _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {Π _ _} {Π _ _} (conuv , confg)
  = ⊑-Π (⊑-⊔-fst conuv) (⊑-F (subsetIsCon ∪-lemma₃ confg) confg (⊑-⊔-fst' confg))
⊑-⊔-fst {𝒰} {⊥} _ = ⊑-refl *
⊑-⊔-fst {𝒰} {𝒰} _ = ⊑-refl *

⊑-⊔-snd' : ∀ {f g u v} → conFinFun (f ∪ g) → (u , v) ∈ g → ⊑-proof (f ∪ g) u v
⊑-⊔-snd' {u = u} {v} (conPairsfg , conElemsfg) uv∈g
  with (conElemsfg {u} (∪-lemma₄ uv∈g))
... | (conu , conv)
  = record { sub = (u , v) ∷ ∅
           ; preable = conAssoc' {u} conu
           ; sub⊆g = ⊆-trans (⊆-lemma₅ uv∈g) ∪-lemma₄
           ; pre⊑u = botElimRight conu
           ; v⊑post = botIntroRight conv
           }

⊑-⊔-snd : ∀ {u v} → con (u ⊔ v) → v ⊑ (u ⊔ v)
⊑-⊔-snd {⊥} conuv = ⊑-refl conuv
⊑-⊔-snd {0ᵤ} {⊥} _ = ⊑-⊥ *
⊑-⊔-snd {0ᵤ} {0ᵤ} _ = ⊑-refl *
⊑-⊔-snd {s _} {⊥} conuv = ⊑-⊥ conuv
⊑-⊔-snd {s _} {s _} conuv = ⊑-s (⊑-⊔-snd conuv)
⊑-⊔-snd {ℕ} {⊥} conuv = ⊑-⊥ *
⊑-⊔-snd {ℕ} {ℕ} conuv = ⊑-refl *
⊑-⊔-snd {F _} {⊥} conuv = ⊑-⊥ conuv
⊑-⊔-snd {F _} {F _} conuv
  = ⊑-F (subsetIsCon ∪-lemma₄ conuv) conuv (⊑-⊔-snd' conuv)
⊑-⊔-snd {Π _ _} {⊥} conuv = ⊑-⊥ conuv
⊑-⊔-snd {Π _ _} {Π _ _} (conuv , confg)
  = ⊑-Π (⊑-⊔-snd conuv) (⊑-F (subsetIsCon ∪-lemma₄ confg) confg (⊑-⊔-snd' confg))
⊑-⊔-snd {𝒰} {⊥} _ = ⊑-⊥ *
⊑-⊔-snd {𝒰} {𝒰} _ = ⊑-refl *
