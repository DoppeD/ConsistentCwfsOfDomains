{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.DefProof
  (𝐴 𝐵 : Ty) where

open import Appmap.Lemmata
open import Base.ConFinFun 𝐴 𝐵
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵

-- Contains the proof that 𝐹 𝑓 ⊑ 𝐹 𝑓′ in the arrow
-- neighborhood system if and only if the smallest approximable
-- mapping containing 𝑓′ also contains 𝑓. We show that the
-- two propositions imply one another.

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
pre↦post : (𝑓 : NbhFinFun 𝐴 𝐵) → (preable𝑓 : Preable 𝑓) →
           (postable𝑓 : Postable 𝑓) → (γ : tAppmap [ 𝐴 ] [ 𝐵 ]) →
           𝑓 ⋐ γ → [ γ ] ⟪ pre 𝑓 preable𝑓 ⟫ ↦ ⟪ post 𝑓 postable𝑓 ⟫
pre↦post ∅ _ _ γ _ = Appmap.↦-bottom γ
pre↦post (< x , y > ∷ 𝑓′) (pre-cons preable𝑓′ conxpre𝑓′)
  (post-cons postable𝑓′ conypost𝑓′) γ (⋐-intro p)
  = appmapLemma₃ {γ = γ} ⟪ x ⟫ ⟪ pre 𝑓′ preable𝑓′ ⟫
    ⟪ y ⟫ ⟪ post 𝑓′ _ ⟫ toValCon toValCon (p x y here)
    (pre↦post 𝑓′ preable𝑓′ postable𝑓′ γ (⋐-intro (λ x′ y′ x′y′∈𝑓′ →
    p x′ y′ (there x′y′∈𝑓′))))

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
    -- mapping has been derived from (x , y) ∈ 𝑓
    -- or the approximable mapping axioms.
    idGen : ∀ x y → [ γ ] ⟪ x ⟫ ↦ ⟪ y ⟫ → InductivelyGenerated 𝑓 x y

exp⇒smallest' : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) → {con𝑓 : ConFinFun 𝑓} →
                {con𝑓′ : ConFinFun 𝑓′} →
                (γ : SmallestAppmap 𝑓′) → 𝐹 𝑓 con𝑓 ⊑ₑ 𝐹 𝑓′ con𝑓′ →
                ∀ x y → < x , y > ∈ 𝑓 → [ SmallestAppmap.γ γ ] ⟪ x ⟫ ↦ ⟪ y ⟫
exp⇒smallest' 𝑓 𝑓′ γ (⊑ₑ-intro₂ _ _ _ con p) x y xy∈𝑓
  with (p x y xy∈𝑓)
exp⇒smallest' 𝑓 𝑓′ γ (⊑ₑ-intro₂ _ _ _ con p) x y xy∈𝑓
  | record { sub = 𝑓″
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable𝑓″
           ; postablesub = postable𝑓″
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = Appmap.↦-↓closed γ' y⊑post𝑓″ γx↦post
   where γ' = SmallestAppmap.γ γ
         pre𝑓″⊑x = ⊑ᵥ-cons [ 𝐴 ] ⟪ pre 𝑓″ preable𝑓″ ⟫ ⟪ x ⟫ pre⊑x
                   ⊑ᵥ-nil
         y⊑post𝑓″ = ⊑ᵥ-cons [ 𝐵 ] ⟪ y ⟫ ⟪ post 𝑓″ postable𝑓″ ⟫ y⊑post ⊑ᵥ-nil
         γpre𝑓″↦post𝑓″ = pre↦post 𝑓″ preable𝑓″ postable𝑓″ γ'
                         (⋐-lemma 𝑓″ 𝑓′ sub⊆𝑓 γ' (SmallestAppmap.cont γ))
         γx↦post = Appmap.↦-mono γ' pre𝑓″⊑x γpre𝑓″↦post𝑓″

exp⇒smallest : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) → {con𝑓 : ConFinFun 𝑓} →
               {con𝑓′ : ConFinFun 𝑓′} →
               (γ : SmallestAppmap 𝑓′) → 𝐹 𝑓 con𝑓 ⊑ₑ 𝐹 𝑓′ con𝑓′ →
               𝑓 ⋐ SmallestAppmap.γ γ
exp⇒smallest 𝑓 𝑓′ γ 𝑓⊑𝑓′
  = ⋐-intro (exp⇒smallest' 𝑓 𝑓′ γ 𝑓⊑𝑓′)

smallest⇒exp' : (𝑓′ : NbhFinFun 𝐴 𝐵) → {con : ConFinFun 𝑓′} →
                (γ : SmallestAppmap 𝑓′) →
                ∀ x y → InductivelyGenerated 𝑓′ x y →
                ⊑ₑ-proof 𝑓′ con x y
smallest⇒exp' 𝑓′ γ x y (ig-inset _ _ xy∈𝑓′)
  = record
      { sub = < x , y > ∷ ∅
      ; sub⊆𝑓 = ⊆-lemma₄ < x , y > xy∈𝑓′ ∅-isSubset
      ; preablesub = pre-cons pre-nil (con⊥₂ 𝐴)
      ; postablesub = post-cons post-nil (con⊥₂ 𝐵)
      ; y⊑post = NbhSys.⊑-⊔-fst 𝐵 (con⊥₂ 𝐵)
      ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴) (con⊥₂ 𝐴)
      }
smallest⇒exp' 𝑓′ γ x y (ig-bot _)
  = record
      { sub = ∅
      ; sub⊆𝑓 = ∅-isSubset
      ; preablesub = pre-nil
      ; postablesub = post-nil
      ; y⊑post = NbhSys.⊑-⊥ 𝐵
      ; pre⊑x = NbhSys.⊑-⊥ 𝐴
      }      
smallest⇒exp' 𝑓′ {con} γ x y (ig-mono _ x′ _ idGen x′⊑x)
  = record
      { sub = ⊑ₑ-proof.sub rec
      ; sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 rec
      ; preablesub = ⊑ₑ-proof.preablesub rec
      ; postablesub = ⊑ₑ-proof.postablesub rec
      ; y⊑post = ⊑ₑ-proof.y⊑post rec
      ; pre⊑x = NbhSys.⊑-trans 𝐴 (⊑ₑ-proof.pre⊑x rec) x′⊑x
      }
  where rec = smallest⇒exp' 𝑓′ {con} γ x′ y idGen
smallest⇒exp' 𝑓′ {con} γ x y (ig-↓clo _ _ y′ idGen y⊑y′)
  = record
      { sub = ⊑ₑ-proof.sub rec
      ; sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 rec
      ; preablesub = ⊑ₑ-proof.preablesub rec
      ; postablesub = ⊑ₑ-proof.postablesub rec
      ; y⊑post = NbhSys.⊑-trans 𝐵 y⊑y′ (⊑ₑ-proof.y⊑post rec)
      ; pre⊑x = ⊑ₑ-proof.pre⊑x rec
      }
  where rec = smallest⇒exp' 𝑓′ {con} γ x y′ idGen
smallest⇒exp' 𝑓′ {con} γ x _ (ig-↑dir _ y y′ idGeny idGeny′ conyy′)
  with (smallest⇒exp' 𝑓′ {con} γ x y idGeny) | smallest⇒exp' 𝑓′ {con} γ x y′ idGeny′
... | record { sub = sub
             ; sub⊆𝑓 = sub⊆𝑓′
             ; preablesub = preable
             ; postablesub = postable
             ; y⊑post = y⊑post
             ; pre⊑x = pre⊑x
             }
    | record { sub = sub′
             ; sub⊆𝑓 = sub′⊆𝑓′
             ; preablesub = preable′
             ; postablesub = postable′
             ; y⊑post = y⊑post′
             ; pre⊑x = pre′⊑x
             }
  = record
      { sub = sub ∪ sub′
      ; sub⊆𝑓 = ∪⊆𝑓
      ; preablesub = preable∪
      ; postablesub = postable∪
      ; y⊑post = NbhSys.⊑-trans 𝐵 (⊑-⊔-lemma₃ 𝐵 _ conpost y⊑post y⊑post′)
                 (postLemma₁ postable postable′ _ _ )
      ; pre⊑x = NbhSys.⊑-trans 𝐴 (preLemma₁ preable preable′ _ _)
                (NbhSys.⊑-⊔ 𝐴 pre⊑x pre′⊑x consubs)
      }
  where γγ = SmallestAppmap.γ γ
        γ⋐𝑓′ = SmallestAppmap.cont γ
        preable∪ = preUnionLemma preable preable′ pre⊑x pre′⊑x
        consubs = NbhSys.Con-⊔ 𝐴 pre⊑x pre′⊑x
        ∪⊆𝑓 = ∪-lemma₁ sub⊆𝑓′ sub′⊆𝑓′
        conpostval = Appmap.↦-con γγ
                     (pre↦post sub preable postable γγ
                     (⋐-lemma sub 𝑓′ sub⊆𝑓′ γγ γ⋐𝑓′))
                     (pre↦post sub′ preable′ postable′ γγ
                     (⋐-lemma sub′ 𝑓′ sub′⊆𝑓′ γγ γ⋐𝑓′))
                     (toValCon {conxy = consubs})
        conpost = fromValCon {conxy = conpostval}
        postable∪ = postUnionLemma postable postable′
                    (NbhSys.⊑-⊔-fst 𝐵 conpost)
                    (NbhSys.⊑-⊔-snd 𝐵 _)

smallest⇒exp : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
               (con𝑓 : ConFinFun 𝑓) → (con𝑓′ : ConFinFun 𝑓′) →
               (γ : SmallestAppmap 𝑓′) →
               𝑓 ⋐ SmallestAppmap.γ γ →
               𝐹 𝑓 con𝑓 ⊑ₑ 𝐹 𝑓′ con𝑓′
smallest⇒exp 𝑓 𝑓′ con𝑓 con𝑓′ γ (⋐-intro p)
  = ⊑ₑ-intro₂ 𝑓 𝑓′ con𝑓 con𝑓′ (λ x y xy∈𝑓 →
    smallest⇒exp' 𝑓′ {con𝑓′} γ x y
    (SmallestAppmap.idGen γ x y (p x y xy∈𝑓)))
