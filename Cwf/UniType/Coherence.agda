module Cwf.UniType.Coherence where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition

coherence' : ∀ {f g h} → conFinFun (f ∪ g) → conFinFun (f ∪ h) → conFinFun (g ∪ h) →
             conFinFun (f ∪ (g ∪ h))
coherence' {f} {g} {h} conf∪g conf∪h cong∪h uv∈ u′v′∈ conuu′
  with (∪-lemma₂ {𝑓 = f} uv∈) | ∪-lemma₂ {𝑓 = f} u′v′∈
coherence' conf∪g _ _ _ _ conuu′ | inl uv∈f | inl u′v′∈f =
  conf∪g (∪-lemma₆ uv∈f) (∪-lemma₆ u′v′∈f) conuu′
coherence' {g = g} conf∪g conf∪h _ _ _ conuu′ | inl uv∈f | inr u′v′∈g∪h
  with (∪-lemma₂ {𝑓 = g} u′v′∈g∪h)
... | inl u′v′∈g = conf∪g (∪-lemma₆ uv∈f) (∪-lemma₇ u′v′∈g) conuu′
... | inr u′v′∈h = conf∪h (∪-lemma₆ uv∈f) (∪-lemma₇ u′v′∈h) conuu′
coherence' {g = g} conf∪g conf∪h _ _ _ conuu′ | inr uv∈g∪h | inl u′v′∈f
  with (∪-lemma₂ {𝑓 = g} uv∈g∪h)
... | inl uv∈g = conf∪g (∪-lemma₇ uv∈g) (∪-lemma₆ u′v′∈f) conuu′
... | inr uv∈h = conf∪h (∪-lemma₇ uv∈h) (∪-lemma₆ u′v′∈f) conuu′
coherence' {g = g} _ _ cong∪h _ _ conuu′ | inr uv∈g∪h | inr u′v′∈g∪h = cong∪h uv∈g∪h u′v′∈g∪h conuu′

coherence : ∀ {u v w} → con (u ⊔ v) → con (u ⊔ w) → con (v ⊔ w) → con (u ⊔ (v ⊔ w))
coherence {⊥} _ _ convw = convw
coherence {0ᵤ} {⊥} _ conuw _ = conuw
coherence {0ᵤ} {0ᵤ} {⊥} _ _ _ = *
coherence {0ᵤ} {0ᵤ} {0ᵤ} _ _ _ = *
coherence {s _} {⊥} _ conuw _ = conuw
coherence {s _} {s _} {⊥} conuv _ _ = conuv
coherence {s u} {s _} {s _} = coherence {u}
coherence {ℕ} {⊥} _ conuw _ = conuw
coherence {ℕ} {ℕ} {⊥} _ _ _ = *
coherence {ℕ} {ℕ} {ℕ} _ _ _ = *
coherence {F _} {⊥} _ conuw _ = conuw
coherence {F _} {F _} {⊥} conuv _ _ = conuv
coherence {F f} {F _} {F _} = coherence' {f = f}
coherence {Π _ _} {⊥} _ conuw _ = conuw
coherence {Π _ _} {Π _ _} {⊥} conuv _ _ = conuv
coherence {Π u f} {Π _ _} {Π _ _} (conuv , confg) (conuw , confh) (convw , congh) =
  (coherence {u = u} conuv conuw convw , coherence' {f = f} confg confh congh )
coherence {𝒰} {⊥} {w} _ conuw _ = conuw
coherence {𝒰} {𝒰} {⊥} _ _ _ = *
coherence {𝒰} {𝒰} {𝒰} _ _ _ = *

conAssoc : ∀ {u v w} → con (u ⊔ (v ⊔ w)) → con ((u ⊔ v) ⊔ w)
conAssoc = {!!}

conLemma₁ : ∀ {u v} → con (u ⊔ v) → con u
conLemma₁ {⊥} _ = *
conLemma₁ {0ᵤ} _ = *
conLemma₁ {s _} {⊥} conuv = conuv
conLemma₁ {s u} {s _} conuv = conLemma₁ {u} conuv
conLemma₁ {ℕ} _ = *
conLemma₁ {F _} {⊥} conuv = conuv
conLemma₁ {F f} {F g} confg uv∈f u′v′∈f conuu′
  = confg (∪-lemma₆ uv∈f) (∪-lemma₆ u′v′∈f) conuu′
conLemma₁ {Π _ _} {⊥} conuv = conuv
conLemma₁ {Π u f} {Π v g} (conuv , confg)
  = conLemma₁ {u} conuv , subsetIsCon (∪-lemma₆ {𝑓′ = g}) confg
conLemma₁ {𝒰} _ = *

conLemma₂ : ∀ {u v} → con (u ⊔ v) → con v
conLemma₂ {v = ⊥} _ = *
conLemma₂ {v = 0ᵤ} _ = *
conLemma₂ {⊥} {s _} conuv = conuv
conLemma₂ {s u} {s _} conuv = conLemma₂ {u} conuv
conLemma₂ {v = ℕ} _ = *
conLemma₂ {⊥} {F _} conuv = conuv
conLemma₂ {F f} {F g} confg uv∈g u′v′∈g conuu′
  = confg (∪-lemma₇ uv∈g) (∪-lemma₇ u′v′∈g) conuu′
conLemma₂ {⊥} {Π _ _} conuv = conuv
conLemma₂ {Π u f} {Π v g} (conuv , confg)
  = conLemma₂ {u} conuv , subsetIsCon (∪-lemma₇ {𝑓′ = g}) confg
conLemma₂ {v = 𝒰} _ = *
conLemma₂ {⊥} {incons} conuv = conuv
conLemma₂ {0ᵤ} {incons} conuv = conuv
conLemma₂ {s u} {incons} conuv = conuv
conLemma₂ {ℕ} {incons} conuv = conuv
conLemma₂ {F conuv₁} {incons} conuv = conuv
conLemma₂ {Π u conuv₁} {incons} conuv = conuv
conLemma₂ {𝒰} {incons} conuv = conuv
conLemma₂ {incons} {incons} conuv = conuv

af : {f g : FinFun Nbh Nbh} → ∀ {x} → x ∈ (f ∪ g) → x ∈ (g ∪ f)
af = {!!}

conFinFunSym : ∀ {f g} → conFinFun (f ∪ g) → conFinFun (g ∪ f)
conFinFunSym {f} conf∪g uv∈∪ u′v′∈∪ conuu′
  = conf∪g (af {g = f} uv∈∪) (af {g = f} u′v′∈∪) conuu′

conSym : ∀ {u v} → con (u ⊔ v) → con (v ⊔ u)
conSym {⊥} {⊥} _ = *
conSym {⊥} {0ᵤ} _ = *
conSym {⊥} {s _} conuv = conuv
conSym {⊥} {ℕ} _ = *
conSym {⊥} {F _} conuv = conuv
conSym {⊥} {Π _ _} conuv = conuv
conSym {⊥} {𝒰} _ = *
conSym {0ᵤ} {⊥} _ = *
conSym {0ᵤ} {0ᵤ} _ = *
conSym {s _} {⊥} conuv = conuv
conSym {s u} {s _} conuv = conSym {u} conuv
conSym {ℕ} {⊥} _ = *
conSym {ℕ} {ℕ} _ = *
conSym {F _} {⊥} conuv = conuv
conSym {F f} {F g} conuv = conFinFunSym {f} conuv
conSym {Π _ _} {⊥} conuv = conuv
conSym {Π u f} {Π _ _} (conuv , confg) = (conSym {u} conuv) , conFinFunSym {f} confg
conSym {𝒰} {⊥} _ = *
conSym {𝒰} {𝒰} _ = *

bigo : ∀ {u v w} → con (u ⊔ (v ⊔ w)) → con (u ⊔ v)
bigo {⊥} {v} conuv = conLemma₁ {v} conuv
bigo {0ᵤ} {v} x = {!!}
bigo {s u} {v} x = {!!}
bigo {ℕ} x = {!!}
bigo {F x₁} x = {!!}
bigo {Π u x₁} x = {!!}
bigo {𝒰} x = {!!}

asd : ∀ {f} → conFinFun f → con (pre f) → con (post f)
asd {∅} _ _ = *
asd {(u , v) ∷ ∅} conf conupref′ = {!!} -- Agh...need to ensure that every element is consistent itself
asd {(u , v) ∷ ((u′ , v′) ∷ f′)} conf conupref′ =
  coherence {u = v} {v = v′} {w = post f′} (conf here (there here) (conLemma₁ {u = u ⊔ u′} (conAssoc {u = u} conupref′)))
  (asd {f = (u , v) ∷ f′} {!!} {!!})
  (asd {f = ((u′ , v′) ∷ f′)} (subsetIsCon ⊆-lemma₃ conf) (conLemma₂ {u} conupref′))
-- Get con (u ⊔ pre f′) by
