{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.lam.Lemmata where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.lam.Relation
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.DomainUcwf.UniType.PrePost

open import Agda.Builtin.Nat

private
  variable
    𝑡 : uTerm (suc n)

pre-biggest : ∀ 𝑓 x y → (x , y) ∈ 𝑓 →
              [ UniType ] x ⊑ pre 𝑓
pre-biggest ((x , y) ∷ 𝑓) x y here
  = NbhSys.⊑-⊔-fst UniType con-all
pre-biggest ((x′ , y′) ∷ 𝑓′) x y (there xy∈𝑓′)
  = ⊑-⊔-lemma₅ UniType (pre-biggest 𝑓′ x y xy∈𝑓′) con-all

shrinklam : ∀ {𝑥 𝑓 𝑓′} → 𝑓 ⊆ 𝑓′ →
            [ 𝑡 ] 𝑥 lam↦ (λᵤ 𝑓′) → [ 𝑡 ] 𝑥 lam↦ (λᵤ 𝑓)
shrinklam {𝑓 = 𝑓} 𝑓⊆𝑓′ (lam↦-intro₂ p)
  = lam↦-intro₂ (λ xy∈𝑓 → p (𝑓⊆𝑓′ xy∈𝑓))

↓closed-lemma' : ∀ 𝑥 𝑓 → [ 𝑡 ] 𝑥 lam↦ (λᵤ 𝑓) →
                 ∀ x y → (x , y) ∈ 𝑓 →
                 [ 𝑡 ] ⟪ pre 𝑓 ,, 𝑥 ⟫ ↦ y
↓closed-lemma' {n} {𝑡 = 𝑡} 𝑥 (x ∷ 𝑓′) (lam↦-intro₂ p)
  x′ y′ x′y′∈𝑓
  = Appmap.↦-mono 𝑡 a𝑥⊑p𝑓𝑥 (p x′y′∈𝑓)
  where a⊑p𝑓 = pre-biggest (x ∷ 𝑓′) x′ y′ x′y′∈𝑓
        a𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (nToCtx (suc n)) a⊑p𝑓
                 (NbhSys.⊑-refl (ValNbhSys _))

↓closed-lemma : ∀ 𝑥 𝑓 →
                [ 𝑡 ] 𝑥 lam↦ (λᵤ 𝑓) →
                [ 𝑡 ] ⟪ pre 𝑓 ,, 𝑥 ⟫ ↦ (post 𝑓)
↓closed-lemma {𝑡 = 𝑡} 𝑥 ∅ _ = Appmap.↦-bottom 𝑡
↓closed-lemma {n} {𝑡 = 𝑡} 𝑥 ((x , y) ∷ 𝑓′) lam𝑡𝑥↦𝑓
  = Appmap.↦-↑directed 𝑡 𝑡pre𝑓'↦y 𝑡𝑓𝑥↦p𝑓′ con-all
  where 𝑓' = (x , y) ∷ 𝑓′
        𝑡pre𝑓'↦y = ↓closed-lemma' 𝑥 𝑓' lam𝑡𝑥↦𝑓  x y here
        p𝑓′⊑p𝑓 = NbhSys.⊑-⊔-snd UniType con-all
        p𝑓′𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (nToCtx (suc n)) p𝑓′⊑p𝑓
                   (NbhSys.⊑-refl (ValNbhSys _))
        𝑡p𝑓′𝑥↦p𝑓′ = ↓closed-lemma 𝑥 𝑓′
                    (shrinklam (λ 𝑦∈𝑓′ → there 𝑦∈𝑓′)
                    lam𝑡𝑥↦𝑓)
        𝑡𝑓𝑥↦p𝑓′ = Appmap.↦-mono 𝑡 p𝑓′𝑥⊑p𝑓𝑥 𝑡p𝑓′𝑥↦p𝑓′
