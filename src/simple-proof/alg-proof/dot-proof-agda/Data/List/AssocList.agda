{-# OPTIONS --safe #-}

module Data.List.AssocList where

open import Data.List as List
open import Data.Product
open import Data.List.Containment
open import Data.List.NonEmpty as List⁺
open import Function
open import Level

mapVal : ∀ {a b}{A : Set a}{B : A → Set b}{C : A → Set b} →
         (f : (x : A) → B x → C x) →
         List (Σ A B) → List (Σ A C)
mapVal f [] = []
mapVal f ((proj₁ , proj₂) ∷ l) = (proj₁ , f proj₁ proj₂) ∷ mapVal f l


module _ {a} {A : Set a} where

  data uniq : List A → Set a where
    instance
      empty : uniq []
      grow  : ∀ {h l} → h ∉ l → uniq l → uniq $ h ∷ l


  record uniq⁺ (l : List⁺ A) : Set a where
    field
      uq : uniq $ toList l


module _ {k v} (K : Set k) (V : K → Set v) where
  private
    kv = k ⊔ v

  AssocList : Set kv
  AssocList = List (Σ K V)

  dom : AssocList → List K
  dom = List.map proj₁

  Map : Set kv
  Map = Σ AssocList (uniq ∘ dom)

  AssocList⁺ : Set kv
  AssocList⁺ = List⁺ (Σ K V)

  dom⁺ : AssocList⁺ → List⁺ K
  dom⁺ = List⁺.map proj₁

  Map⁺ : Set kv
  Map⁺ = Σ AssocList⁺ (uniq⁺ ∘ dom⁺)
