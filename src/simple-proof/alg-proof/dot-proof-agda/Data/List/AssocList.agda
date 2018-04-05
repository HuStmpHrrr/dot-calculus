{-# OPTIONS --safe #-}

module Data.List.AssocList where

open import Data.List
open import Data.Product

mapVal : ∀ {a b}{A : Set a}{B : A → Set b}{C : A → Set b} →
         (f : (x : A) → B x → C x) →
         List (Σ A B) → List (Σ A C)
mapVal f [] = []
mapVal f ((proj₁ , proj₂) ∷ l) = (proj₁ , f proj₁ proj₂) ∷ mapVal f l
