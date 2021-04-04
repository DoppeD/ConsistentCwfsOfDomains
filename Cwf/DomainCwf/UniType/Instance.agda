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

data _≈_ : ConNbh → ConNbh → Set where
  ≈-⊥ : ∀ {i j} → (conNbh {i} ⊥ *) ≈ (conNbh {j} ⊥ *)
  ≈-0 : ∀ {i j} → (conNbh {i} 0ᵤ *) ≈ (conNbh {j} 0ᵤ *)

donk : ∀ {i j} → {i≤j : i ≤ j} → {u v : Nbh {i}} → u ⊑ v →
       (liftNbh {j = j} i≤j u) ⊑ (liftNbh {j = j} i≤j v)
dank : ∀ {i j} → {i≤j : i ≤ j} → {f g : FinFun {i}} → (F f) ⊑ (F g) →
       ∀ {u v} → (u , v) ∈ (liftFinFun i≤j f) → ⊑-proof (liftFinFun i≤j g) u v
donk (⊑-bot conv) = ⊑-bot {!!}
donk ⊑-0 = ⊑-0
donk (⊑-s u⊑v) = ⊑-s (donk u⊑v)
donk ⊑-ℕ = ⊑-ℕ
donk {i≤j = ≤-suc _} (⊑-F conf cong p) = ⊑-F {!!} {!!} (dank (⊑-F conf cong p))
donk (⊑-rfl u⊑v) = ⊑-rfl (donk u⊑v)
donk (⊑-I U⊑U′ u⊑u′ v⊑v′) = ⊑-I (donk U⊑U′) (donk u⊑u′) (donk v⊑v′)
donk (⊑-Π U f) = {!!}
donk ⊑-𝒰 = ⊑-𝒰

dank {f = (u , v) ∷ f′} (⊑-F _ _ p) u′v′∈↑f = {!!}

-- Say that (conNbh {i} u _) ⊑ (conNbh {j} v _) is defined by lifting both u and v to i + j taking u ⊑ v.
-- We can then define equivalence classes, so that u {i} ≈ u′ {j} if they only differ by the "sizes" i and j.
-- Then prove that if u ≈ u' and v ≈ v', then u ⊑ v iff u' ⊑ v'

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

UniType : NbhSys
NbhSys.Nbh UniType = ConNbh
NbhSys._⊑_ UniType (conNbh {i} u _) (conNbh {j} v _)
  = (liftNbh {j = i + j} asd u) ⊑ (liftNbh dsa v)
NbhSys.Con UniType (conNbh {i} u _) (conNbh {j} v _)
  = con ((liftNbh {j = i + j} asd u) ⊔ (liftNbh dsa v))
NbhSys._⊔_[_] UniType (conNbh u _) (conNbh v _) conuv = {!!}
NbhSys.⊥ UniType = conNbh {0} ⊥ *
NbhSys.Con-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = {!!}
NbhSys.⊑-refl UniType {conNbh _ conu} = {!!}
NbhSys.⊑-trans UniType {conNbh {i} u _} {conNbh {j} v _} {conNbh {k} w _} u⊑v v⊑w = {!!}
NbhSys.⊑-⊥ UniType {conNbh _ conu} = {!!}
NbhSys.⊑-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = {!!}
NbhSys.⊑-⊔-fst UniType {conNbh _ _} {conNbh _ _} = {!!}
NbhSys.⊑-⊔-snd UniType {conNbh _ _} {conNbh _ _} = {!!}

{-
UniType : NbhSys
NbhSys.Nbh UniType = ConNbh
NbhSys._⊑_ UniType (conNbh u _) (conNbh v _) = u ⊑ v
NbhSys.Con UniType (conNbh u _) (conNbh v _) = con (u ⊔ v)
NbhSys._⊔_[_] UniType (conNbh u _) (conNbh v _) conuv = conNbh (u ⊔ v) conuv
NbhSys.⊥ UniType = conNbh ⊥ *
NbhSys.Con-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = Con-⊔
NbhSys.⊑-refl UniType {conNbh _ conu} = ⊑-refl conu
NbhSys.⊑-trans UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = ⊑-trans
NbhSys.⊑-⊥ UniType {conNbh _ conu} = ⊑-⊥ conu
NbhSys.⊑-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = ⊑-⊔
NbhSys.⊑-⊔-fst UniType {conNbh _ _} {conNbh _ _} = ⊑-⊔-fst
NbhSys.⊑-⊔-snd UniType {conNbh _ _} {conNbh _ _} = ⊑-⊔-snd
-}
