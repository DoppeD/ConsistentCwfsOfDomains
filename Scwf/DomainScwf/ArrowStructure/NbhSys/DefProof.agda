{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.DefProof
  (𝐴 𝐵 : Ty) where

open import Appmap.Lemmata
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵

-- Contains the proof that 𝐹 𝑓 ⊑ 𝐹 𝑓′ in the arrow
-- neighborhood system if and only if the smallest approximable
-- mapping containing 𝑓′ also contains 𝑓. We show that the
-- two propositions imply one another.

-- The "containment" relation.
data _⋐_ (𝑓 : NbhFinFun 𝐴 𝐵) (γ : Appmap 𝐴 𝐵) :
         Set where
  ⋐-intro : (∀ {x y} → < x , y > ∈ 𝑓 → [ γ ] x ↦ y) →
            𝑓 ⋐ γ

-- If an approximable mapping γ contains 𝑓, then it
-- contains any subset 𝑓' of 𝑓.
⋐-lemma : (𝑓' 𝑓 : NbhFinFun 𝐴 𝐵) → 𝑓' ⊆ 𝑓 →
          (γ : Appmap 𝐴 𝐵) →
          𝑓 ⋐ γ → 𝑓' ⋐ γ
⋐-lemma 𝑓' 𝑓 𝑓'⊆𝑓 γ (⋐-intro p)
  = ⋐-intro λ xy∈𝑓' → p (𝑓'⊆𝑓 xy∈𝑓')

-- If 𝑓 is contained in the mapping γ, then γ maps (pre 𝑓)
-- to (post 𝑓)
pre↦post : (𝑓 : NbhFinFun 𝐴 𝐵) → (preable𝑓 : Preable 𝑓) →
           (postable𝑓 : Postable 𝑓) → (γ : Appmap 𝐴 𝐵) →
           𝑓 ⋐ γ → [ γ ] (pre 𝑓 preable𝑓) ↦ (post 𝑓 postable𝑓)
pre↦post ∅ _ _ γ _ = Appmap.↦-bottom γ
pre↦post (< x , y > ∷ 𝑓′) (pre-cons preable𝑓′ conxpre𝑓′)
  (post-cons postable𝑓′ conypost𝑓′) γ (⋐-intro p)
  = appmapLemma₃ {γ = γ} x (pre 𝑓′ preable𝑓′) y
    (post 𝑓′ _) _ _ (p here)
    (pre↦post 𝑓′ preable𝑓′ postable𝑓′ γ (⋐-intro (λ x′y′∈𝑓′ →
    p (there x′y′∈𝑓′))))

-- A predicate describing that γ maps x to y iff either (x, y) ∈ 𝑓
-- or γ : x ↦ y is inductively generated from the approximable mapping
-- axioms.
data AppmapClosure (𝑓 : NbhFinFun 𝐴 𝐵)
                   (con𝑓 : ConFinFun 𝑓) : ∀ x y → Set where
  ig-inset : ∀ {x y} → < x , y > ∈ 𝑓 →
             AppmapClosure 𝑓 con𝑓 x y
  ig-bot  : ∀ {x} →
            AppmapClosure 𝑓 con𝑓 x (NbhSys.⊥ 𝐵)
  ig-mono : ∀ {x x′ y} → [ 𝐴 ] x′ ⊑ x → AppmapClosure 𝑓 con𝑓 x′ y →
            AppmapClosure 𝑓 con𝑓 x y
  ig-↓clo : ∀ {x y y′} → [ 𝐵 ] y ⊑ y′ → AppmapClosure 𝑓 con𝑓 x y′ →
            AppmapClosure 𝑓 con𝑓 x y
  ig-↑dir : ∀ {x y y′} → AppmapClosure 𝑓 con𝑓 x y →
            AppmapClosure 𝑓 con𝑓 x y′ → (con : NbhSys.Con 𝐵 y y′) →
            AppmapClosure 𝑓 con𝑓 x ([ 𝐵 ] y ⊔ y′ [ con ])

smallest⇒exp' : (𝑓′ : NbhFinFun 𝐴 𝐵) → {con : ConFinFun 𝑓′} →
                ∀ {x y} → AppmapClosure 𝑓′ con x y →
                ⊑ₑ-proof 𝑓′ con x y
smallest⇒exp' 𝑓′ {x = x} {y} (ig-inset xy∈𝑓′)
  = record
      { sub = < x , y > ∷ ∅
      ; sub⊆𝑓 = ⊆-lemma₄ xy∈𝑓′ ∅-isSubset
      ; preablesub = pre-cons pre-nil (con⊥₂ 𝐴)
      ; postablesub = post-cons post-nil (con⊥₂ 𝐵)
      ; y⊑post = NbhSys.⊑-⊔-fst 𝐵 (con⊥₂ 𝐵)
      ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴)
                (NbhSys.⊑-⊥ 𝐴) (con⊥₂ 𝐴)
      }
smallest⇒exp' 𝑓′ ig-bot
  = record
      { sub = ∅
      ; sub⊆𝑓 = ∅-isSubset
      ; preablesub = pre-nil
      ; postablesub = post-nil
      ; y⊑post = NbhSys.⊑-⊥ 𝐵
      ; pre⊑x = NbhSys.⊑-⊥ 𝐴
      }
smallest⇒exp' 𝑓′ {con} {x} {y} (ig-mono {x′ = x′} x′⊑x idGen)
  = record
      { sub = ⊑ₑ-proof.sub rec
      ; sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 rec
      ; preablesub = ⊑ₑ-proof.preablesub rec
      ; postablesub = ⊑ₑ-proof.postablesub rec
      ; y⊑post = ⊑ₑ-proof.y⊑post rec
      ; pre⊑x = NbhSys.⊑-trans 𝐴 (⊑ₑ-proof.pre⊑x rec) x′⊑x
      }
  where rec = smallest⇒exp' 𝑓′ {con} {x′} {y} idGen
smallest⇒exp' 𝑓′ {con} {x} {y} (ig-↓clo {y′ = y′} y⊑y′ idGen)
  = record
      { sub = ⊑ₑ-proof.sub rec
      ; sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 rec
      ; preablesub = ⊑ₑ-proof.preablesub rec
      ; postablesub = ⊑ₑ-proof.postablesub rec
      ; y⊑post = NbhSys.⊑-trans 𝐵 y⊑y′ (⊑ₑ-proof.y⊑post rec)
      ; pre⊑x = ⊑ₑ-proof.pre⊑x rec
      }
  where rec = smallest⇒exp' 𝑓′ {con} {x} {y′} idGen
smallest⇒exp' 𝑓′ {cff p} {x} (ig-↑dir {y = y} {y′}
  idGeny idGeny′ conyy′)
  with (smallest⇒exp' 𝑓′ {cff p} {x} {y} idGeny)
  | smallest⇒exp' 𝑓′ {cff p} {x} {y′} idGeny′
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
      ; y⊑post = NbhSys.⊑-trans 𝐵
                 (⊑-⊔-lemma₃ 𝐵 _ conpost y⊑post y⊑post′)
                 (postLemma₃ postable postable′ _ _ )
      ; pre⊑x = NbhSys.⊑-trans 𝐴 (preLemma₃ preable preable′ _ _)
                (NbhSys.⊑-⊔ 𝐴 pre⊑x pre′⊑x conpre)
      }
  where preable∪ = preUnionLemma preable preable′ pre⊑x pre′⊑x
        conpre = NbhSys.Con-⊔ 𝐴 pre⊑x pre′⊑x
        ∪⊆𝑓 = ∪-lemma₁ sub⊆𝑓′ sub′⊆𝑓′
        postable∪ = p (∪-lemma₁ sub⊆𝑓′ sub′⊆𝑓′) preable∪
        conpost = NbhSys.Con-⊔ 𝐵
                  (postLemma₁ {𝑓 = sub} {postable∪ = postable∪})
                  (postLemma₂ {𝑓′ = sub′} {postable∪ = postable∪})

appmapClosureCon : ∀ {𝑓 con𝑓 x y x′ y′} →
                   AppmapClosure 𝑓 con𝑓 x y →
                   AppmapClosure 𝑓 con𝑓 x′ y′ →
                   NbhSys.Con 𝐴 x x′ →
                   NbhSys.Con 𝐵 y y′
appmapClosureCon {𝑓} {cff p} {x} {y} {x′} {y′}
  apcloxy apclox′y′ conxx′
  with (smallest⇒exp' 𝑓 {x = x} {y} apcloxy)
  | smallest⇒exp' 𝑓 {x = x′} {y′} apclox′y′
... | record { sub = sub
             ; sub⊆𝑓 = sub⊆𝑓
             ; preablesub = preable
             ; postablesub = postable
             ; y⊑post = y⊑post
             ; pre⊑x = pre⊑x
             }
    | record { sub = sub′
             ; sub⊆𝑓 = sub′⊆𝑓
             ; preablesub = preable′
             ; postablesub = postable′
             ; y⊑post = y′⊑post′
             ; pre⊑x = pre′⊑x′
             }
  = NbhSys.Con-⊔ 𝐵 {z = post (sub ∪ sub′) postable∪} y⊑post∪ y′⊑post∪
  where x⊔x′ = [ 𝐴 ] x ⊔ x′ [ conxx′ ]
        presub⊑x⊔x′ = ⊑-⊔-lemma₄ 𝐴 pre⊑x conxx′
        presub′⊑x⊔x′ = ⊑-⊔-lemma₅ 𝐴 pre′⊑x′ conxx′
        preable∪ = preUnionLemma preable preable′ presub⊑x⊔x′
                   presub′⊑x⊔x′
        postable∪ = p (∪-lemma₁ sub⊆𝑓 sub′⊆𝑓) preable∪
        y⊑post∪ = NbhSys.⊑-trans 𝐵 y⊑post
                  (postLemma₁ {𝑓 = sub} {postable∪ = postable∪})
        y′⊑post∪ = NbhSys.⊑-trans 𝐵 y′⊑post′
                   (postLemma₂ {𝑓′ = sub′} {postable∪ = postable∪})

SmallestAppmap : (𝑓 : NbhFinFun 𝐴 𝐵) → ConFinFun 𝑓 → Appmap 𝐴 𝐵
Appmap._↦_ (SmallestAppmap 𝑓 con𝑓)      = AppmapClosure 𝑓 con𝑓
Appmap.↦-mono (SmallestAppmap 𝑓 _)      = ig-mono
Appmap.↦-bottom (SmallestAppmap 𝑓 _)    = ig-bot
Appmap.↦-↓closed (SmallestAppmap 𝑓 _)   = ig-↓clo
Appmap.↦-↑directed (SmallestAppmap 𝑓 _) = ig-↑dir
Appmap.↦-con (SmallestAppmap 𝑓 _)       = appmapClosureCon

smallest⇒exp : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
               (con𝑓 : ConFinFun 𝑓) →
               (con𝑓′ : ConFinFun 𝑓′) →
               𝑓 ⋐ SmallestAppmap 𝑓′ con𝑓′ →
               𝐹 𝑓 con𝑓 ⊑ₑ 𝐹 𝑓′ con𝑓′
smallest⇒exp 𝑓 𝑓′ con𝑓 con𝑓′ (⋐-intro p)
  = ⊑ₑ-intro₂ con𝑓 con𝑓′ (λ xy∈𝑓 →
    smallest⇒exp' 𝑓′ {con𝑓′} (p xy∈𝑓))

exp⇒smallest' : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) → ∀ {con𝑓 con𝑓′} →
                𝐹 𝑓 con𝑓 ⊑ₑ 𝐹 𝑓′ con𝑓′ →
                ∀ {x y} → < x , y > ∈ 𝑓 →
                [ SmallestAppmap 𝑓′ con𝑓′ ] x ↦ y
exp⇒smallest' 𝑓 𝑓′ (⊑ₑ-intro₂ _ con p) xy∈𝑓 with (p xy∈𝑓)
exp⇒smallest' 𝑓 𝑓′ (⊑ₑ-intro₂ _ con p) xy∈𝑓
  | record { sub = 𝑓″
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable𝑓″
           ; postablesub = postable𝑓″
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = Appmap.↦-↓closed γ' y⊑post γx↦post
  where γ' = SmallestAppmap 𝑓′ con
        γpre𝑓″↦post𝑓″ = pre↦post 𝑓″ preable𝑓″ postable𝑓″ γ'
                        (⋐-lemma 𝑓″ 𝑓′ sub⊆𝑓 γ'
                        (⋐-intro ig-inset))
        γx↦post = Appmap.↦-mono γ' pre⊑x γpre𝑓″↦post𝑓″

exp⇒smallest : (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) →
               ∀ {con𝑓 con𝑓′} →
               𝐹 𝑓 con𝑓 ⊑ₑ 𝐹 𝑓′ con𝑓′ →
               𝑓 ⋐ SmallestAppmap 𝑓′ con𝑓′
exp⇒smallest 𝑓 𝑓′ 𝑓⊑𝑓′
  = ⋐-intro (exp⇒smallest' 𝑓 𝑓′ 𝑓⊑𝑓′)
