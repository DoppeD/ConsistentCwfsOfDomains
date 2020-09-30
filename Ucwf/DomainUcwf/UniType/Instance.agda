{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.Instance where

open import Base.Core
open import NbhSys.Definition
open import Ucwf.DomainUcwf.UniType.AxiomProofs
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.Transitivity

open import Agda.Builtin.Nat

UniType : NbhSys
NbhSys.Nbh UniType     = UniNbh
NbhSys._⊑_ UniType     = _⊑ᵤ_
NbhSys.Con UniType     = UniCon
NbhSys._⊔_[_] UniType  = _⊔ᵤ_[_]
NbhSys.⊥ UniType       = ⊥ᵤ
NbhSys.⊑-refl UniType  = ⊑ᵤ-refl
NbhSys.⊑-trans UniType = ⊑ᵤ-trans
NbhSys.⊑-⊥ UniType     = ⊑ᵤ-intro₁
NbhSys.⊑-⊔ UniType     = ⊑ᵤ-⊔ᵤ
NbhSys.⊑-⊔-fst UniType = ⊑ᵤ-⊔ᵤ-fst
NbhSys.⊑-⊔-snd UniType = ⊑ᵤ-⊔ᵤ-snd
NbhSys.Con-⊔ UniType   = λ _ _ → con-all

-- In a ucwf contexts are simply natural numbers.
-- As we want to use approximable mappings as initially
-- defined for scwfs, we define a function that "translates"
-- natural numbers to scwf-contexts.
nToCtx : ∀ (n) → Ctx n
nToCtx zero = []
nToCtx (suc n) = UniType :: (nToCtx n)
