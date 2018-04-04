module Relation.Binary.Containment where

open import Relation.Binary
open import Function
open import Data.Nat renaming (ℕ to Nat)
open import Level renaming (suc to succ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

record IsContainment {a} {Cons : Set a → Set a}
  (_≺_ : ∀ {A : Set a} → A → Cons A → Set a) : Set (succ a) where

  infix 4 _≈_ _≲_

  field
    one        : ∀ {A : Set a} → A → Cons A
    flatten    : ∀ {A : Set a} → Cons (Cons A) → Cons A
    _≈_        : ∀ {A : Set a} → Cons A → Cons A → Set a
    _≲_        : ∀ {A : Set a} → Cons A → Cons A → Set a
    isPreorder : ∀ (A : Set a) → IsPreorder {A = Cons A} _≈_ _≲_

    -- laws
    ≺-flatten  : ∀ {A : Set a} {x : A} {l L}  → x ≺ l → l ≺ L → x ≺ flatten L
    ≺≲-compat  : ∀ {A : Set a} {x : A} {l l′} → x ≺ l → l ≲ l′ → x ≺ l′

record Containment a : Set (succ a) where
  infix 4 _≺_

  field
    Cons          : Set a → Set a
    _≺_           : ∀ {A : Set a} → A → Cons A → Set a
    isContainment : IsContainment {Cons = Cons} _≺_

  open IsContainment isContainment public
    

module ContainmentReasoning {a} (containment : Containment a) where

  open Containment containment
  import Relation.Binary.PreorderReasoning as PreorderReasoning

  preorder : ∀ (A : Set a) → Preorder _ _ _
  preorder A = record { isPreorder = isPreorder A }

  module ≲-Reasoning (A : Set a) = PreorderReasoning (preorder A)

  NestedCons : Nat → (B : Set a) → Set a
  NestedCons zero B    = B
  NestedCons (suc n) B = NestedCons n (Cons B)

  infix  3 _∎
  infixr 2 _≺⟨_⟩_ 
  infix  1 begin_

  flatten-n : ∀ {B} n → NestedCons (suc n) B → Cons B
  flatten-n zero e    = e
  flatten-n (suc n) e = flatten $ flatten-n n e

  -- |this is fairly tricky: we express the data type in GADT
  -- in order to learn about the hierarchy of types in containment
  -- reasoning.
  data _RelatesBy_To_ {B : Set a} : B → (n : Nat) → NestedCons n B → Set a where
    lvl0 : ∀ {x} → x RelatesBy 0 To x
    lvl+ : ∀ {x : B} {n l L} →
             (x≺l : x ≺ l) →
             (cont : l RelatesBy n To L) → x RelatesBy suc n To L
    
  establish : ∀ {B : Set a} {x : B} {n L} →
                x RelatesBy suc n To L → x ≺ flatten-n n L
  establish {n = zero} (lvl+ x≺l lvl0) = x≺l
  establish {n = suc n} (lvl+ x≺l lvl) = ≺-flatten x≺l (establish lvl)


  begin_ : ∀ {B : Set a} {x : B} {n L} →
             x RelatesBy suc n To L → x ≺ flatten-n n L
  begin_ = establish

  _≺⟨_⟩_ : ∀ {A : Set a} (x : A) {l n L} →
             x ≺ l →
             l RelatesBy n To L → x RelatesBy suc n To L
  x ≺⟨ x≺l ⟩ ev = lvl+ x≺l ev

  infixr 2 ≺≲⇒≺
  
  ≺≲⇒≺ : ∀ {A : Set a} (x : A) l {l′ n L} (x≺l : x ≺ l) →
                l ≲ l′ →
                l′ RelatesBy n To L → x RelatesBy suc n To L
  ≺≲⇒≺ x l x≺l l≲l′ ev = lvl+ (≺≲-compat x≺l l≲l′) ev

  syntax ≺≲⇒≺ x l x≺l l≲l′ ev = x ≺⟨ x≺l ⟩- l ≲⟨ l≲l′ ⟩ ev

  _∎ : ∀ {A : Set a} (x : A) → x RelatesBy 0 To x
  _∎ x = lvl0

  private
    reasoning-example₁ : ∀ {A : Set a} (x : A) {l l′} → x ≺ l  → l ≲ l′ → x ≺ l′
    reasoning-example₁ x {l} {l′} x≺l l≲l′ = begin
      x  ≺⟨ x≺l ⟩-
      l  ≲⟨ l≲l′ ⟩
      l′ ∎

    reasoning-example₂ : ∀ {A : Set a} (x : A) {l l′ L} → x ≺ l  → l ≲ l′ → l′ ≺ L → x ≺ flatten L
    reasoning-example₂ x {l} {l′} {L} x≺l l≲l′ l′≺L = begin
      x  ≺⟨ x≺l ⟩-
      l  ≲⟨ l≲l′ ⟩
      l′ ≺⟨ l′≺L ⟩
      L  ∎

    reasoning-example₃ : ∀ {A : Set a} (x : A) {l l′ L Ł} →
                           x ≺ l →
                           l ≺ l′ → l′ ≲ L →
                           L ≺ Ł →
                           x ≺ flatten (flatten Ł)
    reasoning-example₃ x {l} {l′} {L} {Ł} x≺l l≺l′ l′≲L L≺Ł = begin
      x  ≺⟨ x≺l ⟩
      l  ≺⟨ l≺l′ ⟩-
      l′ ≲⟨ l′≲L ⟩
      L  ≺⟨ L≺Ł ⟩
      Ł ∎
