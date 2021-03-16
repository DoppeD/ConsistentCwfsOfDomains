module Cwf.UniType.AppmapClosure where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Coherence
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition
open import Cwf.UniType.Relation

data AppmapClosure (f : FinFun Nbh Nbh) : Nbh → Nbh → Set where
  ac-inset : ∀ {u v} → (u , v) ∈ f → AppmapClosure f u v
  ac-mono : ∀ {u v w} → u ⊑ v → AppmapClosure f u w → AppmapClosure f v w
  ac-bot : ∀ {u} → AppmapClosure f u ⊥
  ac-↓closed : ∀ {u v w} → v ⊑ w → AppmapClosure f u w → AppmapClosure f u v
  ac-↑directed : ∀ {u v w} → con (v ⊔ w) → AppmapClosure f u v → AppmapClosure f u w →
                 AppmapClosure f u (v ⊔ w)

pre↦post : ∀ {f} → conFinFun f → con (pre f) → AppmapClosure f (pre f) (post f)
pre↦post {∅} _ _ = ac-bot
pre↦post {(u , v) ∷ f′} conf conPref with (pre↦post {f′})
... | pref′↦postf′ = ac-mono {u = pre f′} {u ⊔ pre f′} {v ⊔ post f′} {!!} pref′↦postf
  where pref′↦postf = ac-↑directed {u = pre f′} {v} {post f′} (coherence conf conPref) {!!} {!!}

proof₁ : ∀ {f g u v} → (F f) ⊑ (F g) → (u , v) ∈ f → AppmapClosure g u v
proof₁ (⊑-F conf cong f⊑g) uv∈f with (f⊑g uv∈f)
... | record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  = {!!}
