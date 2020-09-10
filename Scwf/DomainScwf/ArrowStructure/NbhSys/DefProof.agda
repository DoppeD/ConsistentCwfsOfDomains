{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.DefProof
  (𝐴 𝐵 : Ty) where

-- Contains the proof that 𝐹 𝑓 ⊑ 𝐹 𝑓′ in the arrow
-- neighborhood system if and only if the smallest approximable
-- mapping containing 𝑓′ also contains 𝑓. We show that the
-- two propositions imply one another.

open import Appmap.Lemmata
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.AxiomProofs 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Lemmata 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.PrePost 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

-- The "containment" relation.
data _⋐_ (𝑓 : NbhFinFun 𝐴 𝐵) (γ : tAppmap [ 𝐴 ] [ 𝐵 ]) :
         Set where
  ⋐-intro : (∀ x y → < x , y > ∈ 𝑓 → [ γ ] ⟪ x ⟫ ↦ ⟪ y ⟫) →
            𝑓 ⋐ γ

-- If an approximable mapping γ contains 𝑓, then it
-- contains any subset 𝑓' of 𝑓.
⋐-lemma : (𝑓' 𝑓 : NbhFinFun 𝐴 𝐵) → 𝑓' ⊆ 𝑓 →
          (γ : tAppmap [ 𝐴 ] [ 𝐵 ]) →
          𝑓 ⋐ γ → 𝑓' ⋐ γ
⋐-lemma 𝑓' 𝑓 𝑓'⊆𝑓 γ (⋐-intro p)
  = ⋐-intro λ x y xy∈𝑓' → p x y (𝑓'⊆𝑓 < x , y > xy∈𝑓')

-- If 𝑓 is contained in the mapping γ, then γ maps (pre 𝑓)
-- to (post 𝑓)
pre↦post : (𝑓 : NbhFinFun 𝐴 𝐵) → (γ : tAppmap [ 𝐴 ] [ 𝐵 ]) →
           𝑓 ⋐ γ → [ γ ] ⟪ pre 𝑓 ⟫ ↦ ⟪ post 𝑓 ⟫
pre↦post ∅ γ _ = Appmap.↦-bottom γ
pre↦post (< x , y > ∷ 𝑓′) γ (⋐-intro p)
  = appmapLemma₃ {γ = γ} ⟪ x ⟫ ⟪ pre 𝑓′ ⟫ ⟪ y ⟫
    ⟪ post 𝑓′ ⟫ (p x y here)
    (pre↦post 𝑓′ γ (⋐-intro (λ x′ y′ x′y′∈𝑓′ →
    p x′ y′ (there x′y′∈𝑓′))))

-- A predicate describing that γ maps x to y iff either (x, y) ∈ 𝑓
-- or γ : x ↦ y is inductively generated from the approximable mapping
-- axioms.
data InductivelyGenerated (γ : tAppmap [ 𝐴 ] [ 𝐵 ])
                          (𝑓 : NbhFinFun 𝐴 𝐵) : ∀ x y → Set where
  ig-inset : ∀ x y → < x , y > ∈ 𝑓 →
             InductivelyGenerated γ 𝑓 x y
  ig-bot  : ∀ x →
            InductivelyGenerated γ 𝑓 x (NbhSys.⊥ 𝐵)
  ig-mono : ∀ x x′ y → InductivelyGenerated γ 𝑓 x′ y → [ 𝐴 ] x′ ⊑ x →
            InductivelyGenerated γ 𝑓 x y
  ig-↓clo : ∀ x y y′ → InductivelyGenerated γ 𝑓 x y′ → [ 𝐵 ] y ⊑ y′ →
            InductivelyGenerated γ 𝑓 x y
  ig-↑dir : ∀ x y y′ → InductivelyGenerated γ 𝑓 x y →
            InductivelyGenerated γ 𝑓 x y′ →
            InductivelyGenerated γ 𝑓 x ([ 𝐵 ] y ⊔ y′)

-- Definition of the smallest mapping containing a function 𝑓.
-- Such a mapping can contain only the relations required
-- in order to satisfy the axioms, and nothing more.
record SmallestAppmap (𝑓 : NbhFinFun 𝐴 𝐵) : Set₁ where
  field
    -- The mapping itself.
    γ : tAppmap [ 𝐴 ] [ 𝐵 ]

    -- 𝑓 is contained in γ.
    cont : 𝑓 ⋐ γ

    -- Whenever γ maps x to y, we have a proof that the
    -- mapping has been derived from (x , y) ∈ 𝑓 or one
    -- of the approximable mapping axioms.
    idGen : ∀ x y → [ γ ] ⟪ x ⟫ ↦ ⟪ y ⟫ → InductivelyGenerated γ 𝑓 x y

smallest⇒exp' : (𝑓′ : NbhFinFun 𝐴 𝐵) →
                (γ : tAppmap [ 𝐴 ] [ 𝐵 ]) →
                ∀ x y → InductivelyGenerated γ 𝑓′ x y →
                ⊑ₑ-proof 𝑓′ x y
smallest⇒exp' 𝑓′ γ x y (ig-inset _ _ xy∈𝑓′)
  = record { sub = < x , y > ∷ ∅
           ; y⊑post = NbhSys.⊑-⊔-fst 𝐵
           ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴)
                     (NbhSys.⊑-⊥ 𝐴)
           ; sub⊆𝑓 = ⊆-lemma₄ < x , y > xy∈𝑓′
                     ∅-isSubset
           }
smallest⇒exp' 𝑓′ γ x .(NbhSys.⊥ 𝐵) (ig-bot _)
  = record { sub = ∅
           ; y⊑post = NbhSys.⊑-⊥ 𝐵
           ; pre⊑x = NbhSys.⊑-⊥ 𝐴
           ; sub⊆𝑓 = ∅-isSubset
           }
smallest⇒exp' 𝑓′ γ x y (ig-mono _ x′ _ igGen x′⊑x)
  = record { sub = ⊑ₑ-proof.sub rec
           ; y⊑post = ⊑ₑ-proof.y⊑post rec
           ; pre⊑x = NbhSys.⊑-trans 𝐴 (⊑ₑ-proof.pre⊑x rec) x′⊑x
           ; sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 rec
           }
  where rec = smallest⇒exp' 𝑓′ γ x′ y igGen
smallest⇒exp' 𝑓′ γ x y (ig-↓clo _ _ y′ idGen y⊑y′)
  = record { sub = ⊑ₑ-proof.sub rec
           ; y⊑post = NbhSys.⊑-trans 𝐵 y⊑y′ (⊑ₑ-proof.y⊑post rec)
           ; pre⊑x = ⊑ₑ-proof.pre⊑x rec
           ; sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 rec
           }
  where rec = smallest⇒exp' 𝑓′ γ x y′ idGen
smallest⇒exp' 𝑓′ γ x _ (ig-↑dir _ y y′ idGeny idGeny′)
  = record { sub = (⊑ₑ-proof.sub rec) ∪ ⊑ₑ-proof.sub rec′
           ; y⊑post = NbhSys.⊑-trans 𝐵
                      (⊑-⊔-lemma₃ 𝐵 (⊑ₑ-proof.y⊑post rec)
                      (⊑ₑ-proof.y⊑post rec′))
                      (postLemma₁ (⊑ₑ-proof.sub rec)
                      (⊑ₑ-proof.sub rec′))
           ; pre⊑x = NbhSys.⊑-trans 𝐴
                     (preLemma₁ (⊑ₑ-proof.sub rec)
                     (⊑ₑ-proof.sub rec′))
                     (NbhSys.⊑-⊔ 𝐴 (⊑ₑ-proof.pre⊑x rec)
                     (⊑ₑ-proof.pre⊑x rec′))
           ; sub⊆𝑓 = ∪-lemma₁ (⊑ₑ-proof.sub⊆𝑓 rec)
                     (⊑ₑ-proof.sub⊆𝑓 rec′)
           }
  where rec = smallest⇒exp' 𝑓′ γ x y idGeny
        rec′ = smallest⇒exp' 𝑓′ γ x y′ idGeny′

smallest⇒exp : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
               (γ : SmallestAppmap 𝑓′) →
               𝑓 ⋐ SmallestAppmap.γ γ →
               𝐹 𝑓 ⊑ₑ 𝐹 𝑓′
smallest⇒exp 𝑓 𝑓′ γ (⋐-intro p)
  = ⊑ₑ-intro₂ 𝑓 𝑓′ λ x y xy∈𝑓 →
      smallest⇒exp' 𝑓′ (SmallestAppmap.γ γ) x y
                       (SmallestAppmap.idGen γ x y (p x y xy∈𝑓))

exp⇒smallest' : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
                (γ : SmallestAppmap 𝑓′) → 𝐹 𝑓 ⊑ₑ 𝐹 𝑓′ →
                ∀ x y → < x , y > ∈ 𝑓 →
                [ SmallestAppmap.γ γ ] ⟪ x ⟫ ↦ ⟪ y ⟫
exp⇒smallest' 𝑓 𝑓′ γ (⊑ₑ-intro₂ _ _ p) x y xy∈𝑓
  with (p x y xy∈𝑓)
exp⇒smallest' 𝑓 𝑓′ γ (⊑ₑ-intro₂ _ _ p) x y xy∈𝑓
  | record { sub = 𝑓″
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           ; sub⊆𝑓 = sub⊆𝑓
           }
  = Appmap.↦-↓closed γ' (⊑ᵥ-cons [ 𝐵 ] ⟪ y ⟫ ⟪ post 𝑓″ ⟫
    y⊑post ⊑ᵥ-nil) γx↦post
  where γ' = SmallestAppmap.γ γ
        pre𝑓″⊑x = ⊑ᵥ-cons [ 𝐴 ] ⟪ pre 𝑓″ ⟫ ⟪ x ⟫ pre⊑x
                  ⊑ᵥ-nil
        γpre𝑓″↦post𝑓″ = pre↦post 𝑓″ γ' (⋐-lemma 𝑓″ 𝑓′ sub⊆𝑓
                        γ' (SmallestAppmap.cont γ))
        γx↦post = Appmap.↦-mono γ' pre𝑓″⊑x γpre𝑓″↦post𝑓″

exp⇒smallest : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
               (γ : SmallestAppmap 𝑓′) → 𝐹 𝑓 ⊑ₑ 𝐹 𝑓′ →
               𝑓 ⋐ SmallestAppmap.γ γ
exp⇒smallest 𝑓 𝑓′ γ 𝑓⊑𝑓′
  = ⋐-intro (exp⇒smallest' 𝑓 𝑓′ γ 𝑓⊑𝑓′)
