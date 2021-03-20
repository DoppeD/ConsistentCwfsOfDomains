dslo : ∀ {i} → {x y z : Nbh {i}} → ∀ {conyz} →
       x ⊑ᵤ y → x ⊑ᵤ z → x ⊑ᵤ (y ⊔ᵤ z [ conyz ])
dslo ⊑ᵤ-bot _ = ⊑ᵤ-bot
dslo ⊑ᵤ-refl-0 ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
dslo ⊑ᵤ-refl-ℕ ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
dslo ⊑ᵤ-refl-𝒰 ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
dslo {conyz = con-s conyz} (⊑ᵤ-s x⊑y) (⊑ᵤ-s x⊑z)
  = ⊑ᵤ-s (dslo x⊑y x⊑z)
dslo {conyz = con-λ cff𝑔∪ℎ} (⊑ᵤ-λ p₁) (⊑ᵤ-λ p₂) = ⊑ᵤ-λ (duff p₁)
dslo {conyz = con-Π conyz cff𝑓′∪𝑓″} (⊑ᵤ-Π x⊑y 𝑓⊑𝑓′) (⊑ᵤ-Π x⊑z 𝑓⊑𝑓″)
  = ⊑ᵤ-Π (dslo x⊑y x⊑z) (dslo {conyz = con-λ cff𝑓′∪𝑓″} 𝑓⊑𝑓′ 𝑓⊑𝑓″)

fdop : ∀ {i} → {𝑓 𝑔 ℎ : FinFun (Nbh {i}) (Nbh {i})} → ∀ {conℎ con𝑓∪ℎ} →
       (∀ {x y} → (x , y) ∈ 𝑔 → λ-proof ℎ conℎ x y) →
       ∀ {x y} → (x , y) ∈ (𝑓 ∪ 𝑔) → λ-proof (𝑓 ∪ ℎ) con𝑓∪ℎ x y
fdop {𝑓 = 𝑓} _ xy∈𝑓∪𝑔 with (∪-lemma₂ {𝑓 = 𝑓} xy∈𝑓∪𝑔)
fdop _ {x} {y} _ | inl xy∈𝑓
  = record
      { sub = (x , y) ∷ ∅
      ; sub⊆𝑓 = ⊆-trans (⊆-lemma₅ xy∈𝑓) ∪-lemma₆
      ; preablesub = pre-cons pre-nil con-⊥₂
      ; postablesub = post-cons post-nil con-⊥₂
      ; y⊑post = ⊑ᵤ-refl
      ; pre⊑x = ⊑ᵤ-refl
      }
fdop p _ | inr xy∈𝑔 with (p xy∈𝑔)
fdop _ _ | inr _
  | record
      { sub = sub
      ; sub⊆𝑓 = sub⊆𝑓
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }
  = record
      { sub = sub
      ; sub⊆𝑓 = ⊆-trans sub⊆𝑓 ∪-lemma₇
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }

fdss : ∀ {i} → {x y z : Nbh {i}} → ∀ {conxy conxz} →
       y ⊑ᵤ z → (x ⊔ᵤ y [ conxy ]) ⊑ᵤ (x ⊔ᵤ z [ conxz ])
fdss {conxz = conxz} ⊑ᵤ-bot = ⊑ᵤ-⊔-fst conxz
fdss {conxz = con-⊥₁} ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
fdss {conxz = con-refl-0} ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
fdss {conxz = con-⊥₁} ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
fdss {conxz = con-refl-ℕ} ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
fdss {conxz = con-⊥₁} ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
fdss {conxz = con-refl-𝒰} ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
fdss {conxy = con-⊥₁} {con-⊥₁} (⊑ᵤ-s x) = ⊑ᵤ-s x
fdss {conxy = con-s conxy} {con-s conxz} (⊑ᵤ-s x) = ⊑ᵤ-s (fdss x)
fdss {conxz = con-⊥₁} (⊑ᵤ-λ x) = ⊑ᵤ-λ x
fdss {conxy = con-λ x₂} {conxz = con-λ x₁} (⊑ᵤ-λ x)
  = ⊑ᵤ-λ (fdop x)
fdss {conxy = con-⊥₁} (⊑ᵤ-Π x x₁) = ⊑ᵤ-Π x x₁
fdss {conxy = con-Π a b} {con-Π c d} (⊑ᵤ-Π x (⊑ᵤ-λ p))
  = ⊑ᵤ-Π (fdss x) (⊑ᵤ-λ (fdop p))

sdfl : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} →
       ∀ {postable𝑓 postable∪} → post 𝑓 postable𝑓 ⊑ᵤ post (𝑓 ∪ 𝑓′) postable∪
sdfl {postable𝑓 = post-nil} {post-nil} = ⊑ᵤ-bot
sdfl {postable𝑓 = post-nil} {post-cons postable∪ x} = ⊑ᵤ-bot
sdfl {𝑓 = (_ , _) ∷ 𝑓} {𝑓′} {post-cons postable𝑓 x} {post-cons postable∪ x₁}
  = fdss (sdfl {𝑓 = 𝑓} {𝑓′})

vcx : ∀ {i} → {x y : Nbh {i}} → 0ₙ ⊑ᵤ x → x ⊑ᵤ y → 0ₙ ⊑ᵤ y
vcx ⊑ᵤ-refl-0 ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0

vcy : ∀ {i} → {x y : Nbh {i}} → ℕ ⊑ᵤ x → x ⊑ᵤ y → ℕ ⊑ᵤ y
vcy ⊑ᵤ-refl-ℕ ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ

vcz : ∀ {i} → {x y : Nbh {i}} → 𝒰 ⊑ᵤ x → x ⊑ᵤ y → 𝒰 ⊑ᵤ y
vcz ⊑ᵤ-refl-𝒰 ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰

aaff : ∀ {i} → {x : Nbh {i}} → ∀ {𝑓 𝑓′ postable𝑓 postable∪} → x ⊑ᵤ post 𝑓 postable𝑓 →
       x ⊑ᵤ post (𝑓 ∪ 𝑓′) postable∪
aaff {x = ⊥} a = ⊑ᵤ-bot
aaff {x = 0ₙ} {𝑓} a = vcx a (sdfl {𝑓 = 𝑓})
-- post 𝑓 ≡ s y and post 𝑓′ ≡ s z.
aaff {x = sᵤ x} a = {!!}
aaff {x = ℕ} {𝑓} a = vcy a (sdfl {𝑓 = 𝑓})
aaff {x = 𝒰} {𝑓} a = vcz a (sdfl {𝑓 = 𝑓})
aaff {x = λᵤ 𝑓 x} a = {!!}
aaff {x = Π x 𝑓 x₁} a = {!!}

tmp : ∀ {i} → {x y : Nbh {i}} → ∀ {𝑓 𝑓′ conxy postable𝑓 postable𝑓′ postable∪} →
      x ⊑ᵤ post 𝑓 postable𝑓 → y ⊑ᵤ post 𝑓′ postable𝑓′ →
      (x ⊔ᵤ y [ conxy ]) ⊑ᵤ post (𝑓 ∪ 𝑓′) postable∪
tmp {conxy = con-⊥₁} {postable𝑓′ = postable𝑓′} {postable∪} _ y⊑post𝑓′
  = ⊥-leftId₁ {!!}
tmp {conxy = con-⊥₂} {postable𝑓 = postable𝑓} {postable∪ = postable∪} x⊑post𝑓 _
  = aaff {postable𝑓 = postable𝑓} {postable∪} x⊑post𝑓
tmp {conxy = con-refl-0} {postable𝑓 = postable𝑓} {postable∪ = postable∪} x⊑post𝑓 y⊑post𝑓′
  = aaff {postable𝑓 = postable𝑓} {postable∪} x⊑post𝑓
tmp {conxy = con-s conxy} x⊑post𝑓 y⊑post𝑓′ = {!!}
tmp {conxy = con-refl-ℕ} {postable𝑓 = postable𝑓} {postable∪ = postable∪} x⊑post𝑓 _
  = aaff {postable𝑓 = postable𝑓} {postable∪} x⊑post𝑓
tmp {conxy = con-refl-𝒰} {postable𝑓 = postable𝑓} {postable∪ = postable∪} x⊑post𝑓 _
  = aaff {postable𝑓 = postable𝑓} {postable∪} x⊑post𝑓
tmp {conxy = con-λ cff𝑓∪𝑔} x⊑post𝑓 y⊑post𝑓′ = {!!}
tmp {conxy = con-Π conxy cff𝑓∪𝑔} x⊑post𝑓 y⊑post𝑓′ = {!!}
