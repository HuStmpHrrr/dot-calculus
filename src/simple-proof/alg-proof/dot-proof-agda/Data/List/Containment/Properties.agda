module Data.List.Containment.Properties where

open import Data.List
open import Data.List.Properties

open import Data.List.Containment.Core
open import Data.Sum
open import Data.Product
open import Function using (_$_ ; _∘_)
open import Data.Empty using (⊥)

open import Relation.Binary.Core hiding (Decidable)
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Decidability

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

  ++⋃ : ∀ l L → l ++ ⋃ L ≡ ⋃ (l ∷ L)
  ++⋃ _ _ = refl

  ⋃++ : ∀ L l → ⋃ L ++ l ≡ ⋃ (L ∷ʳ l)
  ⋃++ [] l       rewrite ++-identityʳ l = refl
  ⋃++ (L ∷ L₁) l rewrite ++-assoc L (⋃ L₁) l
                       | ⋃++ L₁ l       = refl

  ++⋃++ : ∀ l₁ L l₂ → l₁ ++ (⋃ L) ++ l₂ ≡ ⋃ (l₁ ∷ (L ∷ʳ l₂))
  ++⋃++ l₁ L l₂ rewrite ⋃++ L l₂ = refl

  ∈⊆-combine : ∀ {x : A} {l₁ l₂} → x ∈ l₁ → l₁ ⊆ l₂ → x ∈ l₂
  ∈⊆-combine () (∅ l)
  ∈⊆-combine (skip .h x∈l₁) (grow h h∈l l₁⊆l₂) = ∈⊆-combine x∈l₁ l₁⊆l₂
  ∈⊆-combine (found l) (grow h h∈l l₁⊆l₂)      = h∈l

  ∉⊆-unpack : ∀ {x : A} {l₁ l₂} → x ∉ l₂ → l₁ ⊆ l₂ → x ∉ l₁
  ∉⊆-unpack x∉l₂ l₁⊆l₂ = λ x∈l₁ → x∉l₂ $ ∈⊆-combine x∈l₁ l₁⊆l₂

  ⊆-growʳ : ∀ {x : A} {l l′} → l ⊆ l′ → l ⊆ x ∷ l′
  ⊆-growʳ {x} {.[]} (∅ l)                  = ∅ (x ∷ l)
  ⊆-growʳ {x} {.(h ∷ _)} (grow h h∈l l⊆l′) = grow h (skip x h∈l) (⊆-growʳ l⊆l′)

  ⊆-shrinkˡ : ∀ {x : A} {l l′} → x ∷ l ⊆ l′ → l ⊆ l′
  ⊆-shrinkˡ (grow h h∈l ss) = ss

  ⊆-relaxˡ : ∀ {l : List A} l₁ {l₂} → l ⊆ l₂ → l ⊆ l₁ ++ l₂
  ⊆-relaxˡ [] l⊆l₂       = l⊆l₂
  ⊆-relaxˡ (x ∷ l₁) l⊆l₂ = ⊆-growʳ $ ⊆-relaxˡ l₁ l⊆l₂

  ⊆-relaxʳ : ∀ {l : List A} {l₁} l₂ → l ⊆ l₁ → l ⊆ l₁ ++ l₂
  ⊆-relaxʳ l₂ (∅ l)             = ∅ (l ++ l₂)
  ⊆-relaxʳ l₂ (grow h h∈l l⊆l₁) = grow h (∈-relaxʳ l₂ h∈l) $ ⊆-relaxʳ l₂ l⊆l₁

  ⊆-relax : ∀ l₁ {l l′ : List A} l₂ → l ⊆ l′ → l ⊆ l₁ ++ l′ ++ l₂
  ⊆-relax l₁ l₂ l⊆l′ = ⊆-relaxˡ l₁ (⊆-relaxʳ l₂ l⊆l′)

  ⋃L⇒⊆ : ∀ {l : List A} {L} → l ∈ L → l ⊆ ⋃ L
  ⋃L⇒⊆ (skip [] l∈L)          = ⋃L⇒⊆ l∈L
  ⋃L⇒⊆ {l} (skip (x ∷ h) l∈L) = ⊆-growʳ $ ⋃L⇒⊆ (skip h l∈L)
  ⋃L⇒⊆ {[]} (found l₁)        = ∅ $ ⋃ l₁
  ⋃L⇒⊆ {x ∷ l} (found L₁)     = grow x (found $ l ++ ⋃ L₁) (⊆-growʳ $ ⋃L⇒⊆ $ found L₁)

  ⊆-reflexive : _≡_ ⇒ (_⊆_ {a}  {A})
  ⊆-reflexive {[]} refl    = ∅ []
  ⊆-reflexive {x ∷ i} refl = grow x (found i) (⊆-growʳ $ ⊆-reflexive refl)

  ⊆-refl : Reflexive (_⊆_ {a} {A})
  ⊆-refl = ⊆-reflexive refl

  ⊆-trans : Transitive (_⊆_ {a} {A})
  ⊆-trans {.[]} {.l} {k} (∅ l) j⊆k        = ∅ k
  ⊆-trans {.(h ∷ _)} (grow h h∈l i⊆j) j⊆k = grow h (∈⊆-combine h∈l j⊆k) (⊆-trans i⊆j j⊆k)

  instance
    ≡⊆-isPreorder : IsPreorder _≡_ _⊆_
    ≡⊆-isPreorder = record
                   { isEquivalence = isEquivalence
                   ; reflexive     = ⊆-reflexive
                   ; trans         = ⊆-trans
                   }
    
  ≡⊆-preorder : Preorder _ _ _
  ≡⊆-preorder = record { isPreorder = ≡⊆-isPreorder }

  ⊆-enlarge : ∀ {x : A} {l} → x ∉ l → ∃[ l′ ](l ⊆ l′)
  ⊆-enlarge {x} {l} _ = x ∷ l , ⊆-growʳ {x} ⊆-refl

  ⊈-extra : ∀ {{_ : Decidable {A = A} _∈_}} {l : List A} {l′} → l ⊈ l′ → ∃[ x ](x ∉ l′)
  ⊈-extra {[]} {l′} ev with ev (∅ l′)
  ... | ()
  ⊈-extra {x ∷ l} {l′} ev with x ∈? l′
  ... | yes x∈l′ = ⊈-extra $ ev ∘ (grow x x∈l′)
  ... | no  x∉l′ = x , x∉l′


  ≋-refl : Reflexive (_≋_ {a} {A})
  ≋-refl {l} = ⊆-refl , ⊆-refl

  ≋-sym : Symmetric (_≋_ {a} {A})
  ≋-sym (l₁⊆l₂ , l₂⊆l₁) = l₂⊆l₁ , l₁⊆l₂

  ≋-trans : Transitive (_≋_ {a} {A})
  ≋-trans (l₁⊆l₂ , l₂⊆l₁) (l₂⊆l₃ , l₃⊆l₂) = ⊆-trans l₁⊆l₂ l₂⊆l₃ , ⊆-trans l₃⊆l₂ l₂⊆l₁

  ≋-respects-⊆ : _≋_ ⇒ (_⊆_ {a} {A})
  ≋-respects-⊆ l₁≋l₂ = proj₁ l₁≋l₂

  ⊆-antisym : Antisymmetric (_≋_ {A = A}) _⊆_
  ⊆-antisym l₁⊆l₂ l₂⊆l₁ = l₁⊆l₂ , l₂⊆l₁

  ⊂-irrefl : Irreflexive (_≋_ {a} {A}) _⊂_
  ⊂-irrefl x≋y = λ z → proj₂ z (proj₂ x≋y)

  ⊂-trans : Transitive (_⊂_ {A = A})
  ⊂-trans (x⊆y , y⊈x) (y⊆z , z⊈y) = ⊆-trans x⊆y y⊆z , λ z⊆x → z⊈y (⊆-trans z⊆x x⊆y)

  ⊂-respects-≋ : (_⊂_ {A = A}) Respects₂ _≋_
  ⊂-respects-≋ = (λ { (a⊆b , b⊆a) (x⊆a , a⊈x) →
                       ⊆-trans x⊆a a⊆b , λ b⊂x → a⊈x (⊆-trans a⊆b b⊂x)
                    })
                 ,
                 λ { (a⊆b , b⊆a) (x⊆a , a⊈x) →
                     ⊆-trans b⊆a x⊆a , λ a⊆b → a⊈x (⊆-trans a⊆b b⊆a)
                   }

  instance
    ≋-equiv : IsEquivalence (_≋_ {a} {A})
    ≋-equiv = record
              { refl  = ≋-refl
              ; sym   = ≋-sym
              ; trans = ≋-trans
              }

    ≋-decEquiv : ∀ {{_ : Decidable {A = A} _∈_}} → IsDecEquivalence (_≋_ {a} {A})
    ≋-decEquiv = record
                 { isEquivalence = ≋-equiv
                 ; _≟_           = decide
                 }

    ⊆-isPreorder : IsPreorder (_≋_ {a} {A}) _⊆_
    ⊆-isPreorder = record
                    { isEquivalence = ≋-equiv
                    ; reflexive     = ≋-respects-⊆
                    ; trans         = ⊆-trans
                    }

    ⊆-isPartialOrder : IsPartialOrder (_≋_ {a} {A}) _⊆_
    ⊆-isPartialOrder = record
                       { isPreorder = ⊆-isPreorder
                       ; antisym    = ⊆-antisym
                       }

    ⊆-isDecPartialOrder : ∀ {{_ : Decidable {A = A} _∈_}} →
                            IsDecPartialOrder (_≋_ {a} {A}) _⊆_
    ⊆-isDecPartialOrder = record
                          { isPartialOrder = ⊆-isPartialOrder
                          ; _≟_            = decide
                          ; _≤?_           = decide
                          }

    ⊂-isStrictPartialOrder : IsStrictPartialOrder (_≋_ {a} {A}) _⊂_
    ⊂-isStrictPartialOrder = record
                             { isEquivalence = ≋-equiv
                             ; irrefl        = ⊂-irrefl
                             ; trans         = ⊂-trans
                             ; <-resp-≈      = ⊂-respects-≋
                             }

    ⊂-isDecStrictPartialOrder : ∀ {{_ : Decidable {A = A} _∈_}} →
                                  IsDecStrictPartialOrder (_≋_ {a} {A}) _⊂_
    ⊂-isDecStrictPartialOrder = record
                                { isStrictPartialOrder = ⊂-isStrictPartialOrder
                                ; _≟_  = decide
                                ; _<?_ = decide
                                }
  
  ≋-setoid : Setoid _ _
  ≋-setoid = record { isEquivalence = ≋-equiv }

  ≋-decSetoid : ∀ {{_ : Decidable {A = A} _∈_}} → DecSetoid _ _
  ≋-decSetoid = record { isDecEquivalence = ≋-decEquiv }

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = record { isPreorder = ⊆-isPreorder }

  ⊆-poset : Poset _ _ _
  ⊆-poset = record { isPartialOrder = ⊆-isPartialOrder }

  ⊆-decPoset : ∀ {{_ : Decidable {A = A} _∈_}} → DecPoset _ _ _
  ⊆-decPoset = record { isDecPartialOrder = ⊆-isDecPartialOrder }

  ⊂-strictPartialOrder : StrictPartialOrder _ _ _
  ⊂-strictPartialOrder = record { isStrictPartialOrder = ⊂-isStrictPartialOrder }

  ⊂-decStrictPartialOrder : ∀ {{_ : Decidable {A = A} _∈_}} →
                              DecStrictPartialOrder _ _ _
  ⊂-decStrictPartialOrder =
    record { isDecStrictPartialOrder = ⊂-isDecStrictPartialOrder }
