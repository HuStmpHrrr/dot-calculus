{-# OPTIONS --safe #-}

-- this module provides alternative definitions

module Data.List.Containment.Alternatives where

open import Data.Product
open import Data.List
open import Level renaming (suc to succ)
open import Data.List.Containment.Core
  using (_∈_ ; _∈?_ ; skip ; found ; emp ; grow) renaming (_⊆_ to _⊆′_)

open import Relation.Nullary
open import Relation.Binary.Decidability


module _ {a} {A : Set a} where

  infix 4 _⊆_  _⊈_  _⊆?_  _≋_  _!≋_  _≋?_  _⊂_  _⊄_  _⊂?_
  
  _⊆_ : List A → List A → Set a
  l₁ ⊆ l₂ = ∀ h → (h∈l₁ : h ∈ l₁) → h ∈ l₂

  _⊈_ : List A → List A → Set a
  l₁ ⊈ l₂ = ¬ (l₁ ⊆ l₂)

  _≋_ : List A → List A → Set a
  l₁ ≋ l₂ = l₁ ⊆ l₂ × l₂ ⊆ l₁

  _!≋_ : List A → List A → Set a
  l₁ !≋ l₂ = ¬ (l₁ ≋ l₂)

  -- |strictly set order
  _⊂_ : List A → List A → Set a
  l₁ ⊂ l₂ = l₁ ⊆ l₂ × l₂ ⊈ l₁
  
  _⊄_ : List A → List A → Set a
  l₁ ⊄ l₂ = ¬ (l₁ ⊂ l₂)

  instance
    ⊆-dec : ∀ {{_ : Decidable {A = A} _∈_}} → Decidable _⊆_
    ⊆-dec = record
            { dec = ⊆-dec′
            } where
      ⊆-dec′ : (xs ys : List A) → Dec (xs ⊆ ys)
      ⊆-dec′ [] ys                              = yes λ x → λ ()
      ⊆-dec′ (x ∷ xs) ys with x ∈? ys
      ⊆-dec′ (x ∷ xs) ys | yes x∈ys with ⊆-dec′ xs ys
      ⊆-dec′ (x ∷ xs) ys | yes x∈ys | yes xs⊆ys = yes λ { h (skip _ h∈l₁) →
                                                          xs⊆ys h h∈l₁
                                                        ; _ (found _) → x∈ys
                                                        }
      ⊆-dec′ (x ∷ xs) ys | yes x∈ys | no xs⊈ys  = no (λ z → xs⊈ys
                                                           (λ h h∈l₁ → z h (skip x h∈l₁)))
      ⊆-dec′ (x ∷ xs) ys | no x∉ys              = no (λ z → x∉ys (z x (found xs)))

  _⊆?_ : ∀ {{_ : Decidable _⊆_}} (x y : List A) → Dec (x ⊆ y)
  l₁ ⊆? l₂ = dec l₁ l₂

  -- following code says precisely that the functional definition would
  -- be the same as inductive definition, if it's decidable.
  
  instance
    ≋-dec : ∀ {{_ : Decidable {A = A} _∈_}} → Decidable _≋_
    ≋-dec = record
            { dec = ≋-dec′
            } where
      ≋-dec′ : (x y : List A) → Dec (x ≋ y)
      ≋-dec′ xs ys with xs ⊆? ys | ys ⊆? xs
      ≋-dec′ xs ys | yes xs⊆ys | yes ys⊆xs = yes (xs⊆ys , ys⊆xs)
      ≋-dec′ xs ys | yes xs⊆ys | no ys⊈xs  = no (λ z → ys⊈xs (proj₂ z))
      ≋-dec′ xs ys | no xs⊈ys  | yes ys⊆xs = no (λ z → xs⊈ys (proj₁ z))
      ≋-dec′ xs ys | no xs⊈ys  | no ys⊈xs  = no (λ z → ys⊈xs (proj₂ z))

  _≋?_ : ∀ {{_ : Decidable _≋_}} → (x y : List A) → Dec (x ≋ y)
  x ≋? y = dec x y

  instance
    ⊂-dec : ∀ {{_ : Decidable {A = A} _∈_}} → Decidable _⊂_
    ⊂-dec = record
            { dec = ⊂-dec′
            } where
      ⊂-dec′ : (x y : List A) → Dec (x ⊂ y)
      ⊂-dec′ x y with x ⊆? y | y ⊆? x
      ⊂-dec′ x y | yes x⊆y | yes y⊆x = no (λ z → proj₂ z y⊆x)
      ⊂-dec′ x y | yes x⊆y | no y⊈x  = yes (x⊆y , y⊈x)
      ⊂-dec′ x y | no x⊈y  | yes y⊆x = no (λ z → proj₂ z y⊆x)
      ⊂-dec′ x y | no x⊈y  | no y⊈x  = no (λ z → x⊈y (proj₁ z))

  _⊂?_ : ∀ {{_ : Decidable _⊂_}} → (x y : List A) → Dec (x ⊂ y)
  _⊂?_ = dec

  -- functional definition and inductive definition are equivalent.
  -- though it's clear that inductive definition is much clearer
  
  ⊆′⇒⊆ : ∀ {l₁ l₂} → l₁ ⊆′ l₂ → l₁ ⊆ l₂
  ⊆′⇒⊆ (grow .h₁ h∈l l₁⊆′l₂) h (skip h₁ h∈l₁) = ⊆′⇒⊆ l₁⊆′l₂ h h∈l₁
  ⊆′⇒⊆ (grow .h h∈l l₁⊆′l₂) h (found l)       = h∈l

  ⊆⇒⊆′ : ∀ {l₁ l₂} → l₁ ⊆ l₂ → l₁ ⊆′ l₂
  ⊆⇒⊆′ {[]} {l₂} l₁⊆l₂ = emp l₂
  ⊆⇒⊆′ {x ∷ l₁} {l₂} l₁⊆l₂ = grow x (l₁⊆l₂ x (found l₁))
                               (⊆⇒⊆′ (λ h h∈l₁ → l₁⊆l₂ h (skip x h∈l₁)))
