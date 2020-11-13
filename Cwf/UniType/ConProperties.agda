module Cwf.UniType.ConProperties where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

cffSym : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh {i}) (Nbh {i})} →
         ConFinFun (𝑓 ∪ 𝑔) → ConFinFun (𝑔 ∪ 𝑓)
cffSym {𝑓 = 𝑓} (cff p)
  = cff λ xy∈𝑓∪𝑔 x′y′∈𝑓∪𝑔 → p (∪-lemma₈ {𝑓′ = 𝑓} xy∈𝑓∪𝑔)
    (∪-lemma₈ {𝑓′ = 𝑓} x′y′∈𝑓∪𝑔)

conSym : ∀ {i} → {x y : Nbh {i}} → Con x y → Con y x
conSym con-⊥₁ = con-⊥₂
conSym con-⊥₂ = con-⊥₁
conSym con-refl-0 = con-refl-0
conSym (con-s consxsy) = con-s (conSym consxsy)
conSym con-refl-ℕ = con-refl-ℕ
conSym con-refl-𝒰 = con-refl-𝒰
conSym (con-Π {𝑓 = 𝑓} conxy cff𝑓∪𝑔)
  = con-Π (conSym conxy) (cffSym {𝑓 = 𝑓} cff𝑓∪𝑔)
conSym (con-λ {𝑓 = 𝑓} cff∪) = con-λ (cffSym {𝑓 = 𝑓} cff∪)
