module Cwf.UniType.Lemmata where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition
open import Cwf.UniType.Relation

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

getCff : ∀ {i} → {𝑓 : FinFun (Nbh {i}) (Nbh {i})} →
         {x y x′ y′ : Nbh {i}} → ConFinFun 𝑓 →
         (x , y) ∈ 𝑓 → (x′ , y′) ∈ 𝑓 →
         Con x x′ → Con y y′
getCff (cff p) = p
