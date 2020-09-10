{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.lam.Lemmata where

open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.lam.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.DomainUcwf.UniType.PrePost
open import Ucwf.DomainUcwf.UniType.SizedFinFun

open import Agda.Builtin.Nat

private
  variable
    𝑡 : uAppmap (suc n) 1

pre-biggest : ∀ 𝑓 x y → < x , y >ₛ ∈ₛ 𝑓 →
              [ UniType ] x ⊑ pre 𝑓
pre-biggest (< x , y >ₛ ∷ 𝑓) x y here = NbhSys.⊑-⊔-fst UniType
pre-biggest (< x′ , y′ >ₛ ∷ 𝑓′) x y (there xy∈𝑓′)
  = ⊑-⊔-lemma₅ UniType (pre-biggest 𝑓′ x y xy∈𝑓′)

shrinklam : ∀ {𝑥 𝑓 𝑓′} → 𝑓 ⊆ₛ 𝑓′ →
            [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓′ ⟫ → [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓 ⟫
shrinklam {𝑓 = 𝑓} 𝑓⊆𝑓′ (lam↦-intro₂ 𝑥 𝑓′ p)
  = lam↦-intro₂ 𝑥 𝑓 (λ x y xy∈𝑓 →
    p x y (𝑓⊆𝑓′ < x , y >ₛ xy∈𝑓))

↓closed-lemma' : ∀ 𝑥 𝑓 → [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓 ⟫ →
                 ∀ x y → < x , y >ₛ ∈ₛ 𝑓 →
                 [ 𝑡 ] ⟪ pre 𝑓 , 𝑥 ⟫ ↦ ⟪ y ⟫
↓closed-lemma' {n} {𝑡 = 𝑡} 𝑥 (x ∷ 𝑓′) (lam↦-intro₂ _ _ p)
  x′ y′ x′y′∈𝑓
  = Appmap.↦-mono 𝑡 a𝑥⊑p𝑓𝑥 (p x′ y′ x′y′∈𝑓)
  where a⊑p𝑓 = pre-biggest (x ∷ 𝑓′) x′ y′ x′y′∈𝑓
        a𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (nToCtx (suc n)) ⟪ x′ , 𝑥 ⟫
                 ⟪ pre (x ∷ 𝑓′) , 𝑥 ⟫ a⊑p𝑓
                 (NbhSys.⊑-refl (ValNbhSys _))

↓closed-lemma : ∀ 𝑥 𝑓 →
                [ 𝑡 ] 𝑥 lam↦ ⟪ λᵤ 𝑓 ⟫ →
                [ 𝑡 ] ⟪ pre 𝑓 , 𝑥 ⟫ ↦ ⟪ post 𝑓 ⟫
↓closed-lemma {𝑡 = 𝑡} 𝑥 ∅ _ = Appmap.↦-bottom 𝑡
↓closed-lemma {n} {𝑡 = 𝑡} 𝑥 (< x , y >ₛ ∷ 𝑓′) lam𝑡𝑥↦𝑓
  = Appmap.↦-↑directed 𝑡 𝑡pre𝑓'↦y 𝑡𝑓𝑥↦p𝑓′
  where 𝑓' = < x , y >ₛ ∷ 𝑓′
        𝑡pre𝑓'↦y = ↓closed-lemma' 𝑥 𝑓' lam𝑡𝑥↦𝑓  x y here
        p𝑓′⊑p𝑓 = NbhSys.⊑-⊔-snd UniType
        p𝑓′𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (nToCtx (suc n))
                   ⟪ pre 𝑓′ , 𝑥 ⟫ ⟪ pre 𝑓' , 𝑥 ⟫ p𝑓′⊑p𝑓
                   (NbhSys.⊑-refl (ValNbhSys _))
        𝑡p𝑓′𝑥↦p𝑓′ = ↓closed-lemma 𝑥 𝑓′
                    (shrinklam (λ 𝑦 𝑦∈𝑓′ → there 𝑦∈𝑓′)
                    lam𝑡𝑥↦𝑓)
        𝑡𝑓𝑥↦p𝑓′ = Appmap.↦-mono 𝑡 p𝑓′𝑥⊑p𝑓𝑥 𝑡p𝑓′𝑥↦p𝑓′
