{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.Instance where

open import Base.Core
open import Cwf.DomainCwf.UniType.AxiomProofs
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.Transitivity
open import NbhSys.Definition

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data ConNbh : Set where
  conNbh : ∀ {i} → (u : Nbh {i}) → con u → ConNbh

data _≤_ : Nat → Nat → Set where
  ≤-zero : ∀ {m} → zero ≤ m
  ≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n

liftNbh : ∀ {i j} → i ≤ j → Nbh {i} → Nbh {j}
liftFinFun : ∀ {i j} → i ≤ j → FinFun {i} → FinFun {j}

liftNbh _ ⊥ = ⊥
liftNbh _ 0ᵤ = 0ᵤ
liftNbh i≤j (s u) = s (liftNbh i≤j u)
liftNbh _ ℕ = ℕ
liftNbh (≤-suc i≤j) (F f) = F (liftFinFun i≤j f)
liftNbh i≤j (refl u) = refl (liftNbh i≤j u)
liftNbh i≤j (I U u v) = I (liftNbh i≤j U) (liftNbh i≤j u) (liftNbh i≤j v)
liftNbh (≤-suc i≤j) (Π U f) = Π (liftNbh i≤j U) (liftFinFun i≤j f)
liftNbh _ 𝒰 = 𝒰
liftNbh _ incons = incons

liftFinFun i≤j ∅ = ∅
liftFinFun i≤j ((u , v) ∷ f′) = (liftNbh i≤j u , liftNbh i≤j v) ∷ (liftFinFun i≤j f′)

asd : ∀ {m n} → m ≤ (m + n)
asd {zero} {n} = ≤-zero
asd {suc m} {n} = ≤-suc asd

dsa : ∀ {m n} → n ≤ (m + n)
dsa {zero} {n} = n≤n
  where n≤n : ∀ {n} → n ≤ n
        n≤n {zero} = ≤-zero
        n≤n {suc n} = ≤-suc n≤n 
dsa {suc m} {zero} = ≤-zero
dsa {suc m} {suc n} = ≤-suc {!!}

data _⊑*_ : ConNbh → ConNbh → Set where
  ⊑*-intro : ∀ {i} → {u v : Nbh {i}} → ∀ {conu conv} → u ⊑ v → (conNbh {i} u conu) ⊑* (conNbh {i} v conv)

UniType : NbhSys
NbhSys.Nbh UniType = ConNbh
NbhSys._⊑_ UniType
  = _⊑*_
NbhSys.Con UniType (conNbh {i} u _) (conNbh {j} v _)
  = con ((liftNbh {j = i + j} asd u) ⊔ (liftNbh dsa v))
NbhSys._⊔_[_] UniType (conNbh u _) (conNbh v _) conuv = {!!}
NbhSys.⊥ UniType = conNbh {0} ⊥ *
NbhSys.Con-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = {!!}
NbhSys.⊑-refl UniType {conNbh _ conu} = ⊑*-intro (⊑-refl conu)
NbhSys.⊑-trans UniType {conNbh {i} u _} {conNbh {.i} v _} {conNbh {.i} w _} (⊑*-intro x) (⊑*-intro x₁)
  = ⊑*-intro (⊑-trans x x₁)
NbhSys.⊑-⊥ UniType {conNbh _ conu} = {!!}
NbhSys.⊑-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = {!!}
NbhSys.⊑-⊔-fst UniType {conNbh _ _} {conNbh _ _} = {!!}
NbhSys.⊑-⊔-snd UniType {conNbh _ _} {conNbh _ _} = {!!}
