{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.Lemmata where

open import Base.Core
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.PrePost
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.SizedFinFun

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

lift⊑ᵤ-proof : ∀ {i j} → (𝑓 𝑓′ : FinFunₛ {i}) →
               (x y : UniNbh {j}) → 𝑓 ⊆ₛ 𝑓′ →
               ⊑ᵤ-proof 𝑓 x y → ⊑ᵤ-proof 𝑓′ x y
lift⊑ᵤ-proof 𝑓 𝑓′ x y 𝑓⊆𝑓′
  record { sub = sub
         ; y⊑ᵤpost = y⊑ᵤpost
         ; pre⊑ᵤx = pre⊑ᵤx
         ; sub⊆𝑓′ = sub⊆𝑓′
         }
  = record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = ⊆ₛ-trans sub⊆𝑓′ 𝑓⊆𝑓′
           }

shrink⊑ᵤ : ∀ {i j} → {𝑓 𝑓′ : FinFunₛ {i}} →
           {𝑓″ : FinFunₛ {j}} → λᵤ 𝑓′ ⊑ᵤ λᵤ 𝑓″ → 𝑓 ⊆ₛ 𝑓′ →
           λᵤ 𝑓 ⊑ᵤ λᵤ 𝑓″
shrink⊑ᵤ {𝑓 = 𝑓} {𝑓′} {𝑓″} (⊑ᵤ-intro₂ _ _ p) 𝑓⊆𝑓′
  = ⊑ᵤ-intro₂ 𝑓 𝑓″ (λ x y xy∈𝑓 → p x y (𝑓⊆𝑓′ < x , y >ₛ xy∈𝑓))

∅-⊥ᵤ : ∀ {𝑓} → (λᵤ ∅) ⊑ᵤ (λᵤ 𝑓)
∅-⊥ᵤ {𝑓} = ⊑ᵤ-intro₂ ∅ 𝑓 (λ x y → xy∈∅-abs)

⊑ᵤ-⊔ᵤ-lemma₁ : ∀ {i j} → (x : UniNbh {i}) →
               (y z : UniNbh {j}) → x ⊑ᵤ y → x ⊑ᵤ (y ⊔ᵤ z)
⊑ᵤ-⊔ᵤ-lemma₁ _ y z ⊑ᵤ-intro₁ = ⊑ᵤ-intro₁
⊑ᵤ-⊔ᵤ-lemma₁ (λᵤ 𝑓) (λᵤ 𝑓′) ⊥ᵤ (⊑ᵤ-intro₂ _ _ p)
  = ⊑ᵤ-intro₂ 𝑓 𝑓′ p
⊑ᵤ-⊔ᵤ-lemma₁ (λᵤ 𝑓) (λᵤ 𝑓′) (λᵤ 𝑓″) (⊑ᵤ-intro₂ _ _ p) =
  ⊑ᵤ-intro₂ 𝑓 (𝑓′ ∪ₛ 𝑓″) (λ x′ y′ x′y′∈𝑓 →
    lift⊑ᵤ-proof 𝑓′ (𝑓′ ∪ₛ 𝑓″) x′ y′ (λ q q∈𝑓′ →
      ∪ₛ-lemma₃ q q∈𝑓′) (p x′ y′ x′y′∈𝑓))

⊑ᵤ-⊔ᵤ-lemma₂ : ∀ {i j} → (x : UniNbh {i}) →
               (y z : UniNbh {j}) → x ⊑ᵤ z → x ⊑ᵤ (y ⊔ᵤ z)
⊑ᵤ-⊔ᵤ-lemma₂ _ y z ⊑ᵤ-intro₁ = ⊑ᵤ-intro₁
⊑ᵤ-⊔ᵤ-lemma₂ (λᵤ 𝑓) ⊥ᵤ (λᵤ 𝑓″) (⊑ᵤ-intro₂ _ _ p)
  = ⊑ᵤ-intro₂ 𝑓 𝑓″ p
⊑ᵤ-⊔ᵤ-lemma₂ (λᵤ 𝑓) (λᵤ 𝑓′) (λᵤ 𝑓″) (⊑ᵤ-intro₂ _ _ p)
  = ⊑ᵤ-intro₂ 𝑓 (𝑓′ ∪ₛ 𝑓″) (λ x′ y′ x′y′∈𝑓 →
      lift⊑ᵤ-proof 𝑓″ (𝑓′ ∪ₛ 𝑓″) x′ y′ (λ q q∈𝑓″ →
        ∪ₛ-lemma₄ q q∈𝑓″) (p x′ y′ x′y′∈𝑓))

⊑ᵤ-⊔ᵤ-lemma₃' : ∀ {i j} → {𝑓 𝑓′ : FinFunₛ {i}} →
                {𝑓″ 𝑓‴ : FinFunₛ {j}} → (λᵤ 𝑓) ⊑ᵤ (λᵤ 𝑓″) →
                (λᵤ 𝑓′) ⊑ᵤ (λᵤ 𝑓‴) →
                ∀ x y → < x , y >ₛ ∈ₛ (𝑓 ∪ₛ 𝑓′) →
                ⊑ᵤ-proof (𝑓″ ∪ₛ 𝑓‴) x y
⊑ᵤ-⊔ᵤ-lemma₃' {𝑓 = 𝑓} {𝑓′} _ _ x y xy∈∪
  with (∪ₛ-lemma₂ {𝑓 = 𝑓} < x , y >ₛ xy∈∪)
⊑ᵤ-⊔ᵤ-lemma₃' (⊑ᵤ-intro₂ _ _ p) _ x y _
  | inl xy∈𝑓 with (p x y xy∈𝑓)
⊑ᵤ-⊔ᵤ-lemma₃' {𝑓″ = 𝑓″} {𝑓‴} _ _ _ _ _ | _
  | record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = sub⊆𝑓′
           }
  = record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = λ x′y′ x′y′∈sub →
               ∪ₛ-lemma₃ x′y′ (sub⊆𝑓′ x′y′ x′y′∈sub)
           }
⊑ᵤ-⊔ᵤ-lemma₃' _ (⊑ᵤ-intro₂ _ _ p) x y _
  | inr xy∈𝑓′ with (p x y xy∈𝑓′)
⊑ᵤ-⊔ᵤ-lemma₃' {𝑓″ = 𝑓″} {𝑓‴} _ _ _ _ _ | _
  | record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = sub⊆𝑓′
           }
  = record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = λ x′y′ x′y′∈sub →
               ∪ₛ-lemma₄ x′y′ (sub⊆𝑓′ x′y′ x′y′∈sub)
           }

⊑ᵤ-⊔ᵤ-lemma₃ : ∀ {i j} → (x y : UniNbh {i}) →
               (z w : UniNbh {j}) → x ⊑ᵤ z → y ⊑ᵤ w →
               (x ⊔ᵤ y) ⊑ᵤ (z ⊔ᵤ w)
⊑ᵤ-⊔ᵤ-lemma₃ ⊥ᵤ ⊥ᵤ _ _ _ _ = ⊑ᵤ-intro₁
⊑ᵤ-⊔ᵤ-lemma₃ (λᵤ 𝑓) _ z w x⊑z ⊑ᵤ-intro₁
  = ⊑ᵤ-⊔ᵤ-lemma₁ (λᵤ 𝑓 ⊔ᵤ ⊥ᵤ) z w x⊑z
⊑ᵤ-⊔ᵤ-lemma₃ ⊥ᵤ (λᵤ 𝑓′) z (λᵤ 𝑓⁗) _ y⊑w
  = ⊑ᵤ-⊔ᵤ-lemma₂ (⊥ᵤ ⊔ᵤ λᵤ 𝑓′) z (λᵤ 𝑓⁗) y⊑w
⊑ᵤ-⊔ᵤ-lemma₃ _ _ _ _ (⊑ᵤ-intro₂ 𝑓 𝑓′ p₁) (⊑ᵤ-intro₂ 𝑓″ 𝑓‴ p₂)
  = ⊑ᵤ-intro₂ (𝑓 ∪ₛ 𝑓″) (𝑓′ ∪ₛ 𝑓‴) 𝑓∪𝑓″⊑𝑓′∪𝑓‴
  where 𝑓∪𝑓″⊑𝑓′∪𝑓‴ = ⊑ᵤ-⊔ᵤ-lemma₃' (⊑ᵤ-intro₂ 𝑓 𝑓′ p₁)
                     (⊑ᵤ-intro₂ 𝑓″ 𝑓‴ p₂)

⊔ᵤ-⊥ᵤ-leftid : {i : Size} → (x : UniNbh {i}) → ⊥ᵤ ⊔ᵤ x ≡ x
⊔ᵤ-⊥ᵤ-leftid ⊥ᵤ = refl
⊔ᵤ-⊥ᵤ-leftid (λᵤ 𝑓) = refl

⊔ᵤ-⊥ᵤ-rightid : {i : Size} → (x : UniNbh {i}) → x ⊔ᵤ ⊥ᵤ ≡ x
⊔ᵤ-⊥ᵤ-rightid ⊥ᵤ = refl
⊔ᵤ-⊥ᵤ-rightid (λᵤ 𝑓) = refl

⊔ᵤ-ass' : {i : Size} → {x y : ×ₛ {i}} → {𝑓 𝑓′ : FinFunₛ {i}} →
          x ≡ y → λᵤ 𝑓 ≡ λᵤ 𝑓′ →
          λᵤ (x ∷ 𝑓) ≡ λᵤ (y ∷ 𝑓′)
⊔ᵤ-ass' refl refl = refl

⊔ᵤ-ass : {i : Size} → (x y z : UniNbh {i}) →
         (x ⊔ᵤ y) ⊔ᵤ z ≡ x ⊔ᵤ (y ⊔ᵤ z)
⊔ᵤ-ass ⊥ᵤ ⊥ᵤ z rewrite (⊔ᵤ-⊥ᵤ-leftid (⊥ᵤ ⊔ᵤ z)) = refl
⊔ᵤ-ass ⊥ᵤ (λᵤ 𝑓′) z rewrite (⊔ᵤ-⊥ᵤ-leftid (λᵤ 𝑓′ ⊔ᵤ z))
  = refl
⊔ᵤ-ass (λᵤ 𝑓) ⊥ᵤ ⊥ᵤ = refl
⊔ᵤ-ass (λᵤ 𝑓) ⊥ᵤ (λᵤ 𝑓′) = refl
⊔ᵤ-ass (λᵤ 𝑓) (λᵤ 𝑓′) ⊥ᵤ = refl
⊔ᵤ-ass (λᵤ ∅) (λᵤ 𝑓′) (λᵤ 𝑓″) = refl
⊔ᵤ-ass (λᵤ (< x₁ , x₂ >ₛ ∷ 𝑔)) (λᵤ 𝑓′) (λᵤ 𝑓″)
  = ⊔ᵤ-ass' refl (⊔ᵤ-ass (λᵤ 𝑔) (λᵤ 𝑓′) (λᵤ 𝑓″))

⊔ᵤ-cong : {i : Size} → {x y z w : UniNbh {i}} → x ≡ z →
          y ≡ w → (x ⊔ᵤ y) ≡ (z ⊔ᵤ w)
⊔ᵤ-cong refl refl = refl

post-≡ : {i : Size} → (𝑓 𝑓′ : FinFunₛ {i}) →
         post (𝑓 ∪ₛ 𝑓′) ≡ (post 𝑓 ⊔ᵤ post 𝑓′)
post-≡ ∅ 𝑓′ rewrite (⊔ᵤ-⊥ᵤ-leftid (post 𝑓′)) = refl
post-≡ (< x₁ , x₂ >ₛ ∷ 𝑔) 𝑓′
  rewrite (⊔ᵤ-ass x₂ (post 𝑔) (post 𝑓′))
  = ⊔ᵤ-cong refl (post-≡ 𝑔 𝑓′)

pre-≡ : {i : Size} → (𝑓 𝑓′ : FinFunₛ {i}) →
        pre (𝑓 ∪ₛ 𝑓′) ≡ (pre 𝑓 ⊔ᵤ pre 𝑓′)
pre-≡ ∅ 𝑓′ rewrite (⊔ᵤ-⊥ᵤ-leftid (pre 𝑓′)) = refl
pre-≡ (< x₁ , x₂ >ₛ ∷ 𝑔) 𝑓′
  rewrite (⊔ᵤ-ass x₁ (pre 𝑔) (pre 𝑓′))
  = ⊔ᵤ-cong refl (pre-≡ 𝑔 𝑓′)
