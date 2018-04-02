module List.Containment.Properties where

open import Data.List
open import Data.List.Properties

open import List.Containment.Core
open import Data.Sum
open import Data.Product
open import Function using (_$_ ; _∘_)
open import Data.Empty using (⊥)

-- a pure fact
⊎⇒duality : ∀ {a b} {X Y : Set a} {B : Set b} →
              (X ⊎ Y → B) → (X → B) × (Y → B)
⊎⇒duality ev = (λ x → ev (inj₁ x)) , (λ x → ev (inj₂ x))


×⇒duality : ∀ {a b} {X Y : Set a} {B : Set b} →
              (X → B) × (Y → B) → (X ⊎ Y → B)
×⇒duality ev (inj₁ x) = proj₁ ev x
×⇒duality ev (inj₂ y) = proj₂ ev y


-- Properties about _∈_
module _ {a} {A : Set a} where

  ∈++-dec : ∀ {x : A} {l₁ l₂} → x ∈ l₁ ++ l₂ → x ∈ l₁ ⊎ x ∈ l₂
  ∈++-dec {l₁ = []}     (skip h ev)            = inj₂ (skip h ev)
  ∈++-dec {l₁ = []}     (found l)              = inj₂ (found l)
  ∈++-dec {l₁ = x ∷ l₁} (skip .x ev) with ∈++-dec {l₁ = l₁} ev
  ∈++-dec {_} {x ∷ l₁}  (skip .x ev) | inj₁ x₁ = inj₁ (skip x x₁)
  ∈++-dec {_} {x ∷ l₁}  (skip .x ev) | inj₂ y  = inj₂ y
  ∈++-dec {l₁ = x ∷ l₁} (found .(l₁ ++ _))     = inj₁ (found l₁)

  ∈⊎⇒∈++ : ∀ {x : A} {l₁ l₂} → x ∈ l₁ ⊎ x ∈ l₂ → x ∈ l₁ ++ l₂
  ∈⊎⇒∈++ {l₁ = []}          (inj₁ ())
  ∈⊎⇒∈++ {l₁ = x ∷ l₁}      (inj₁ (skip .x x₁)) = skip x $ ∈⊎⇒∈++ {l₁ = l₁} (inj₁ x₁)
  ∈⊎⇒∈++ {l₁ = x ∷ l₁} {l₂} (inj₁ (found .l₁))  = found (l₁ ++ l₂)
  ∈⊎⇒∈++ {l₁ = []}          (inj₂ y)            = y
  ∈⊎⇒∈++ {l₁ = x ∷ l₁}      (inj₂ y)            = skip x $ ∈⊎⇒∈++ {l₁ = l₁} (inj₂ y)

  ∈-relax : ∀ {x : A} l₁ {l} l₂ → x ∈ l → x ∈ l₁ ++ l ++ l₂
  ∈-relax l₁ _ ev = ∈⊎⇒∈++ {l₁ = l₁} $ inj₂ $ ∈⊎⇒∈++ $ inj₁ ev

  ∈-relaxˡ : ∀ {x : A} l₁ {l} → x ∈ l → x ∈ l₁ ++ l
  ∈-relaxˡ l₁ ev = ∈⊎⇒∈++ {l₁ = l₁} $ inj₂ ev

  ∈-relaxʳ : ∀ {x : A} {l} l₂ → x ∈ l → x ∈ l ++ l₂
  ∈-relaxʳ l₂ ev = ∈⊎⇒∈++ {l₂ = l₂} $ inj₁ ev

  -- dual lemmas for _∉_

  ∉++-dec : ∀ {x : A} {l₁ l₂} → x ∉ l₁ ++ l₂ → x ∉ l₁ × x ∉ l₂
  ∉++-dec ev = ⊎⇒duality $ ev ∘ ∈⊎⇒∈++

  ∉×⇒∉++ : ∀ {x : A} {l₁ l₂} → x ∉ l₁ → x ∉ l₂ → x ∉ l₁ ++ l₂
  ∉×⇒∉++ = curry $ λ x → ×⇒duality x ∘ ∈++-dec

  -- curiously, we can see a strong duality over here.

  ∉-reduce : ∀ {x : A} l₁ {l} l₂ → x ∉ l₁ ++ l ++ l₂ → x ∉ l
  ∉-reduce l₁ l₂ ev = proj₁ $ ∉++-dec $ proj₂ $ ∉++-dec {l₁ = l₁} ev

  ∉-reduceʳ : ∀ {x : A} l₁ {l} → x ∉ l₁ ++ l → x ∉ l
  ∉-reduceʳ l₁ ev = proj₂ $ ∉++-dec {l₁ = l₁} ev

  ∉-reduceˡ : ∀ {x : A} {l} l₂ → x ∉ l ++ l₂ → x ∉ l
  ∉-reduceˡ l₂ ev = proj₁ $ ∉++-dec {l₂ = l₂} ev

  -- higher level containment implication

  ⋃ : List (List A) → List A
  ⋃ = concat

  ∈⋃ : ∀ {x l L} → x ∈ l → l ∈ L → x ∈ ⋃ L
  ∈⋃ {L = (.h ∷ L)} x∈l (skip h l∈L) = ∈-relaxˡ h $ ∈⋃ x∈l l∈L
  ∈⋃ {L = (_ ∷ .L)} x∈l (found L)    = ∈-relaxʳ (⋃ L) x∈l

  ∉⋃ : ∀ {x l L} → x ∉ ⋃ L → l ∈ L → x ∉ l
  ∉⋃ x∉⋃L l∈L x∈l = x∉⋃L $ ∈⋃ x∈l l∈L


