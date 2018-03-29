{-# OPTIONS --safe #-}
module Definitions where

open import Data.Nat renaming (ℕ to Nat)
import Data.List as List
open List
import Data.Product as Prod
open Prod

import Data.Unit
import Data.Empty

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary renaming (Dec to D)
open import Level renaming (suc to succ)

mapVal : ∀ {a b}{A : Set a}{B : A → Set b}{C : A → Set b} →
         (f : (x : A) → B x → C x) →
         List (Σ A B) → List (Σ A C)
mapVal f [] = []
mapVal f ((proj₁ , proj₂) ∷ l) = (proj₁ , f proj₁ proj₂) ∷ mapVal f l

record Var : Set where
  constructor var_
  field
    --| there are countably infinite natural numbers,
    -- therefore it can represent countably infinite variables.
    sig : Nat


Vars : Set
Vars = List Var

module _ {a} (A : Set a) where
  record CanOpen : Set a where
    infix 10 _<_↦_>
    field
      _<_↦_> : A → Nat → Var → A

  record HasFv : Set a where
    field
      fv : A → Vars

  record CanSubst : Set a where
    infix 10 _[_/_]
    field
      _[_/_] : A → Var → Var → A


------------------------------------------
--
--     Definitions go following

data Avar : Set where
  b_ : Nat → Avar
  f_ : Var → Avar

record TrmLabel : Set where
  field
    lab : Nat

record TypLabel : Set where
  field
    lab : Nat

data Label : Set where
  trm : TrmLabel → Label
  typ : TypLabel → Label


data Typ : Set

infix 7 _⋯_
record DecTyp : Set where
  inductive
  constructor _⋯_
  field
    lb : Typ
    ub : Typ

record DecTrm : Set where
  inductive
  field
    Ttr : Typ

Dec : Label → Set
Dec (trm _) = DecTrm
Dec (typ _) = DecTyp

Decs : Set
Decs = List (Σ Label Dec)

infix 7 _·_ all[_]_ μ[_]
data Typ where
  ⊤ : Typ
  ⊥ : Typ
  _·_ : (x : Avar) → (T : TypLabel) → Typ
  all[_]_ : (T : Typ) → (U : Typ) → Typ
  μ[_] : (DS : Decs) → Typ


data Trm : Set
data Val : Set

record DefTyp : Set where
  inductive
  field
    Ty : Typ

record DefTrm : Set where
  inductive
  field
    tr : Trm

Def : Label → Set
Def (trm x) = DefTrm
Def (typ x) = DefTyp

Defs : Set
Defs = List (Σ Label Def)

data Trm where
  var_ : Avar → Trm
  val_ : Val → Trm
  _·_ : Avar → TrmLabel → Trm
  _!$!_ : Avar → Avar → Trm
  llet_iin_ : Trm → Trm → Trm

data Val where
  ν[_]<_> : Decs → Defs → Val
  Λ[_]<_> : Typ → Trm → Val

open CanOpen {{...}} public
open DecTyp public
open DecTrm public

--| open from zero
_<0↦_> : ∀ {a} {A : Set a} → A → {{_ : CanOpen A}} → Var → A
a <0↦ v > = a < 0 ↦ v >
infix 10 _<0↦_>

instance
  OpenAvar : CanOpen Avar
  _<_↦_> {{OpenAvar}} (b x) n v with x ≟ n
  ... | yes p = f v
  ... | no ¬p = b n
  _<_↦_> {{OpenAvar}} (f x) n v = f x


instance
  OpenTyp : CanOpen Typ
  OpenDecTyp : CanOpen DecTyp
  OpenDecTrm : CanOpen DecTrm
  OpenDecs : CanOpen Decs

  _<_↦_> {{OpenTyp}} ⊤ n v = ⊤
  _<_↦_> {{OpenTyp}} ⊥ n v = ⊥
  _<_↦_> {{OpenTyp}} (x · T) n v = x < n ↦ v > · T
  _<_↦_> {{OpenTyp}} (all[ T ] U) n v = all[ T < n ↦ v > ] U < suc n ↦ v >
  _<_↦_> {{OpenTyp}} μ[ DS ] n v = μ[ DS < suc n ↦ v > ]
  
  _<_↦_> {{OpenDecTyp}} (lb ⋯ ub) n v = lb < n ↦ v > ⋯ ub < n ↦ v >
  
  _<_↦_> {{OpenDecTrm}} record { Ttr = Ttr } n v = record { Ttr = Ttr < n ↦ v > }

  _<_↦_> {{OpenDecs}} [] _ _ = []
  _<_↦_> {{OpenDecs}} ((trm x , proj₂) ∷ DS) n v = (trm x , proj₂ < n ↦ v >) ∷ DS
  _<_↦_> {{OpenDecs}} ((typ x , proj₂) ∷ DS) n v = (typ x , proj₂ < n ↦ v >) ∷ DS


open-to-env : Typ → Var → Typ
open-to-env μ[ DS ] v = μ[ DS < 0 ↦ v > ]
open-to-env T v = T <0↦ v >
