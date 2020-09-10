{-# OPTIONS --safe #-}

open import Base.Core
open import Scwf.DomainScwf.Appmap.Definition

open import Agda.Builtin.Nat

module Scwf.DomainScwf.ArrowStructure.lam.Lemmata
  (𝐴 𝐵 : Ty)
  {n : Nat}
  {Γ : Ctx n}
  (𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ]) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Lemmata 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.PrePost 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

shrinkLam : ∀ {𝑥} → 𝑓 ⊆ 𝑓′ → [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓′ ⟫ →
            [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 ⟫
shrinkLam {𝑓 = 𝑓} 𝑓⊆𝑓′ (lam↦-intro₂ 𝑥 𝑓′ p)
  = lam↦-intro₂ 𝑥 𝑓 (λ x y xy∈𝑓 → p x y (𝑓⊆𝑓′ < x , y > xy∈𝑓))

↓closedLemma' : {𝑥 : Valuation Γ} → [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 ⟫ →
                ∀ x y → < x , y > ∈ 𝑓 →
                [ 𝑡 ] ⟪ pre 𝑓 , 𝑥 ⟫ ↦ ⟪ y ⟫
↓closedLemma'  {𝑓 = (x ∷ 𝑓′)} {𝑥 = 𝑥} (lam↦-intro₂ _ _ p)
  x′ y′ x′y′∈𝑓
  = Appmap.↦-mono 𝑡 a𝑥⊑p𝑓𝑥 (p x′ y′ x′y′∈𝑓)
  where a⊑p𝑓 = preBiggest (x ∷ 𝑓′) x′ y′ x′y′∈𝑓
        a𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ x′ , 𝑥 ⟫
                 ⟪ pre (x ∷ 𝑓′) , 𝑥 ⟫ a⊑p𝑓
                 (NbhSys.⊑-refl (ValNbhSys _))

↓closedLemma : {𝑥 : Valuation Γ} →
               [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 ⟫ →
               [ 𝑡 ] ⟪ pre 𝑓 , 𝑥 ⟫ ↦ ⟪ post 𝑓 ⟫
↓closedLemma {𝑓 = ∅} _ = Appmap.↦-bottom 𝑡
↓closedLemma {𝑓 = (< x , y > ∷ 𝑓′)} {𝑥 = 𝑥} lam𝑡𝑥↦𝑓
  = Appmap.↦-↑directed 𝑡 𝑡pre𝑓'↦y 𝑡𝑓𝑥↦p𝑓′
  where 𝑓' = < x , y > ∷ 𝑓′
        𝑡pre𝑓'↦y = ↓closedLemma' lam𝑡𝑥↦𝑓 x y here
        p𝑓′⊑p𝑓 = NbhSys.⊑-⊔-snd 𝐴
        p𝑓′𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) ⟪ pre 𝑓′ , 𝑥 ⟫
                   ⟪ pre 𝑓' , 𝑥 ⟫ p𝑓′⊑p𝑓
                   (NbhSys.⊑-refl (ValNbhSys _))
        𝑡p𝑓′𝑥↦p𝑓′ = ↓closedLemma
                    (shrinkLam (λ 𝑦 𝑦∈𝑓′ → there 𝑦∈𝑓′)
                    lam𝑡𝑥↦𝑓)
        𝑡𝑓𝑥↦p𝑓′ = Appmap.↦-mono 𝑡 p𝑓′𝑥⊑p𝑓𝑥 𝑡p𝑓′𝑥↦p𝑓′
