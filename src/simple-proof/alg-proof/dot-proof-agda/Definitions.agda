{-# OPTIONS --safe #-}
module Definitions where

open import Data.Nat renaming (ℕ to Nat)
import Data.List as List
open List
import Data.Product as Prod
import Data.List.NonEmpty as List⁺
open List⁺
open Prod

import Data.Unit
import Data.Empty
open import Function

open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary renaming (Dec to D)
open import Level renaming (suc to succ)

mapVal : ∀ {a b}{A : Set a}{B : A → Set b}{C : A → Set b} →
         (f : (x : A) → B x → C x) →
         List (Σ A B) → List (Σ A C)
mapVal f [] = []
mapVal f ((proj₁ , proj₂) ∷ l) = (proj₁ , f proj₁ proj₂) ∷ mapVal f l

data DesList⁺ {a}(A : Set a) : Set a where
  _∷[] : (hd : A) → DesList⁺ A
  _∷_ : (hd : A) → (tl : List⁺ A) → DesList⁺ A

des-view⁺ : ∀ {a}{A : Set a} → List⁺ A → DesList⁺ A
des-view⁺ (head₁ ∷ []) = head₁ ∷[]
des-view⁺ (head₁ ∷ x ∷ tail₁) = head₁ ∷ x ∷ tail₁

record Var : Set where
  constructor var_
  field
    --| there are countably infinite natural numbers,
    -- therefore it can represent countably infinite variables.
    sig : Nat

Var-≟ : Decidable {A = Var} _≡_
Var-≟ (var sig) (var sig₁) with sig ≟ sig₁
Var-≟ (var sig) (var .sig) | yes refl = yes refl
Var-≟ (var sig) (var sig₁) | no ¬p = no λ { refl → ¬p refl }

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

LDec : Set
LDec = Σ Label Dec

Decs : Set
Decs = List⁺ LDec

infix 7 _·_ Π[_]_ μ[_]
data Typ where
  ⊤ : Typ
  ⊥ : Typ
  _·_ : (x : Avar) → (T : TypLabel) → Typ
  Π[_]_ : (T : Typ) → (U : Typ) → Typ
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

LDef : Set
LDef = Σ Label Def

Defs : Set
Defs = List⁺ LDef

infix 7 var_ val_ _!$!_ llet_iin_
data Trm where
  var_ : Avar → Trm
  val_ : Val → Trm
  _·_ : (x : Avar) → (t : TrmLabel) → Trm
  _!$!_ : (s : Avar) → (t : Avar) → Trm
  llet_iin_ : (s : Trm) → (t : Trm) → Trm

data Val where
  ν[_]<_> : (DS : Decs) → (ds : Defs) → Val
  Λ[_]<_> : (T : Typ) → (t : Trm) → Val

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
  OpenLDec : CanOpen LDec
  OpenDecList : CanOpen (List LDec)
  OpenDecs : CanOpen Decs

  _<_↦_> {{OpenTyp}} ⊤ n v = ⊤
  _<_↦_> {{OpenTyp}} ⊥ n v = ⊥
  _<_↦_> {{OpenTyp}} (x · T) n v = x < n ↦ v > · T
  _<_↦_> {{OpenTyp}} (Π[ T ] U) n v = Π[ T < n ↦ v > ] U < suc n ↦ v >
  _<_↦_> {{OpenTyp}} μ[ DS ] n v = μ[ DS < suc n ↦ v > ]
  
  _<_↦_> {{OpenDecTyp}} (lb ⋯ ub) n v = lb < n ↦ v > ⋯ ub < n ↦ v >
  
  _<_↦_> {{OpenDecTrm}} record { Ttr = Ttr } n v = record { Ttr = Ttr < n ↦ v > }

  _<_↦_> {{OpenLDec}} (trm x , proj₂) n v = trm x , proj₂ < n ↦ v >
  _<_↦_> {{OpenLDec}} (typ x , proj₂) n v = typ x , proj₂ < n ↦ v >

  _<_↦_> {{OpenDecList}} [] n v = []
  _<_↦_> {{OpenDecList}} (x ∷ DS) n v = x < n ↦ v > ∷ DS < n ↦ v >

  _<_↦_> {{OpenDecs}} (hd ∷ tl) n v = hd < n ↦ v > ∷ tl < n ↦ v >


open-typ-to-env : Typ → Var → Typ
open-typ-to-env μ[ DS ] v = μ[ DS <0↦ v > ]
open-typ-to-env T v = T <0↦ v >


instance
  OpenTrm : CanOpen Trm
  OpenVal : CanOpen Val
  OpenDefTyp : CanOpen DefTyp
  OpenDefTrm : CanOpen DefTrm
  OpenLDef : CanOpen LDef
  OpenDefList : CanOpen (List LDef)
  OpenDefs : CanOpen Defs

  _<_↦_> {{OpenTrm}} (var x) n v = var x < n ↦ v >
  _<_↦_> {{OpenTrm}} (val x) n v = val x < n ↦ v >
  _<_↦_> {{OpenTrm}} (x · x₁) n v = x < n ↦ v > · x₁
  _<_↦_> {{OpenTrm}} (x !$! x₁) n v = x < n ↦ v > !$! x₁ < n ↦ v >
  _<_↦_> {{OpenTrm}} (llet t iin t₁) n v = llet t < n ↦ v > iin t₁ < suc n ↦ v >

  _<_↦_> {{OpenVal}} ν[ DS ]< ds > n v = ν[ DS < n ↦ v > ]< ds < n ↦ v > >
  _<_↦_> {{OpenVal}} Λ[ T ]< t > n v = Λ[ T < n ↦ v > ]< t < n ↦ v > >
  
  _<_↦_> {{OpenDefTyp}} record { Ty = Ty } n v = record { Ty = Ty < n ↦ v > }
  
  _<_↦_> {{OpenDefTrm}} record { tr = tr } n v = record { tr = tr < n ↦ v > }
  
  _<_↦_> {{OpenLDef}} (trm x , proj₂) n v = trm x , proj₂ < n ↦ v >
  _<_↦_> {{OpenLDef}} (typ x , proj₂) n v = typ x , proj₂ < n ↦ v >
  
  _<_↦_> {{OpenDefList}} [] n v = []
  _<_↦_> {{OpenDefList}} (x ∷ df) n v = x < n ↦ v > ∷ df < n ↦ v >
  
  _<_↦_> {{OpenDefs}} (hd ∷ tl) n v = hd < n ↦ v > ∷ tl < n ↦ v >
  

open-val-to-env : Val → Var → Val
open-val-to-env ν[ DS ]< df > v = ν[ DS <0↦ v > ]< df <0↦ v > >
open-val-to-env l@(Λ[ _ ]< _ >) v = l <0↦ v >

open HasFv {{...}} public

instance
  FvAvar : HasFv Avar
  fv {{FvAvar}} (b x) = []
  fv {{FvAvar}} (f x) = List.[ x ]

instance
  FvTyp : HasFv Typ
  FvDecTyp : HasFv DecTyp
  FvDecTrm : HasFv DecTrm
  FvLDec : HasFv LDec
  FvDecList : HasFv (List LDec)
  FvDecs : HasFv Decs

  fv {{FvTyp}} ⊤ = []
  fv {{FvTyp}} ⊥ = []
  fv {{FvTyp}} (x · T) = fv x
  fv {{FvTyp}} (Π[ T ] U) = fv T ++ fv U
  fv {{FvTyp}} μ[ DS ] = fv DS
  
  fv {{FvDecTyp}} (lb₁ ⋯ ub₁) = fv lb₁ ++ fv ub₁
  
  fv {{FvDecTrm}} record { Ttr = Ttr } = fv Ttr
  
  fv {{FvLDec}} (trm x , proj₂) = fv proj₂
  fv {{FvLDec}} (typ x , proj₂) = fv proj₂
  
  fv {{FvDecList}} [] = []
  fv {{FvDecList}} (x ∷ t) = fv x ++ fv t
  
  fv {{FvDecs}} (hd ∷ tl) = fv hd ++ fv tl


instance
  FvTrm : HasFv Trm
  FvVal : HasFv Val
  FvDefTyp : HasFv DefTyp
  FvDefTrm : HasFv DefTrm
  FvLDef : HasFv LDef
  FvDefList : HasFv (List LDef)
  FvDefs : HasFv Defs

  fv {{FvTrm}} (var x) = fv x
  fv {{FvTrm}} (val x) = fv x
  fv {{FvTrm}} (x · _) = fv x
  fv {{FvTrm}} (x !$! x₁) = fv x ++ fv x₁
  fv {{FvTrm}} (llet t iin t₁) = fv t ++ fv t₁
  
  fv {{FvVal}} ν[ DS ]< ds > = fv DS ++ fv ds
  fv {{FvVal}} Λ[ T ]< t > = fv T ++ fv t
  
  fv {{FvDefTyp}} record { Ty = Ty } = fv Ty
  fv {{FvDefTrm}} record { tr = tr } = fv tr
  
  fv {{FvLDef}} (trm x , proj₄) = fv proj₄
  fv {{FvLDef}} (typ x , proj₄) = fv proj₄
  
  fv {{FvDefList}} [] = []
  fv {{FvDefList}} (x ∷ t) = fv x ++ fv t
  
  fv {{FvDefs}} (head₁ ∷ tail₁) = fv head₁ ++ fv tail₁


Env : Set
Env = List (Var × Typ)

Sta : Set
Sta = List (Var × Val)

fv-vals : ∀ {a}{A : Set a}{{_ : HasFv A}} → List (Var × A) → Vars
fv-vals l = List.foldr _++_ [] $ List.map (fv ∘ Σ.proj₂) l

instance
  FvEnv : HasFv Env
  fv {{FvEnv}} = fv-vals

instance
  FvSta : HasFv Sta
  fv {{FvSta}} = fv-vals

open CanSubst {{...}} public

instance
  SubstAvar : CanSubst Avar
  _[_/_] {{SubstAvar}} (b x₁) a x = b x₁
  _[_/_] {{SubstAvar}} (f x₁) a x with Var-≟ x₁ x
  ... | yes refl = f a
  ... | no ¬p    = f x₁

instance
  SubstTyp : CanSubst Typ
  SubstDecTyp : CanSubst DecTyp
  SubstDecTrm : CanSubst DecTrm
  SubstLDec : CanSubst LDec
  SubstDecList : CanSubst (List LDec)
  SubstDecs : CanSubst Decs

  _[_/_] {{SubstTyp}} ⊤ a x = ⊤
  _[_/_] {{SubstTyp}} ⊥ a x = ⊥
  _[_/_] {{SubstTyp}} (x₁ · T) a x = x₁ [ a / x ] · T
  _[_/_] {{SubstTyp}} (Π[ T ] U) a x = Π[ T [ a / x ] ] U [ a / x ]
  _[_/_] {{SubstTyp}} μ[ DS ] a x = μ[ DS [ a / x ] ]
  
  _[_/_] {{SubstDecTyp}} (lb₁ ⋯ ub₁) a x = lb₁ [ a / x ] ⋯ ub₁ [ a / x ]
  _[_/_] {{SubstDecTrm}} record { Ttr = Ttr } a x = record { Ttr = Ttr [ a / x ] }
    
  _[_/_] {{SubstLDec}} (trm x₁ , proj₄) a x = trm x₁ , proj₄ [ a / x ]
  _[_/_] {{SubstLDec}} (typ x₁ , proj₄) a x = typ x₁ , proj₄ [ a / x ]
  
  _[_/_] {{SubstDecList}} [] a x = []
  _[_/_] {{SubstDecList}} (x₁ ∷ t) a x = x₁ [ a / x ] ∷ t [ a / x ]
  
  _[_/_] {{SubstDecs}} (head₁ ∷ tail₁) a x = head₁ [ a / x ] ∷ tail₁ [ a / x ]
  

instance
  SubstTrm : CanSubst Trm
  SubstVal : CanSubst Val
  SubstDefTyp : CanSubst DefTyp
  SubstDefTrm : CanSubst DefTrm
  SubstLDef : CanSubst LDef
  SubstDefList : CanSubst (List LDef)
  SubstDefs : CanSubst Defs

  _[_/_] {{SubstTrm}} (var x₁) a x = var x₁ [ a / x ]
  _[_/_] {{SubstTrm}} (val x₁) a x = val x₁ [ a / x ]
  _[_/_] {{SubstTrm}} (x₁ · t) a x = x₁ [ a / x ] · t
  _[_/_] {{SubstTrm}} (t !$! s) a x = t [ a / x ] !$! s [ a / x ]
  _[_/_] {{SubstTrm}} (llet t iin t₁) a x = llet t [ a / x ] iin t₁ [ a / x ]

  _[_/_] {{SubstVal}} ν[ DS ]< ds > a x = ν[ DS [ a / x ] ]< ds [ a / x ] >
  _[_/_] {{SubstVal}} Λ[ T ]< t > a x = Λ[ T [ a / x ] ]< t [ a / x ] >
  
  _[_/_] {{SubstDefTyp}} record { Ty = Ty } a x = record { Ty = Ty [ a / x ] }
  
  _[_/_] {{SubstDefTrm}} record { tr = tr } a x = record { tr = tr [ a / x ] }
  
  _[_/_] {{SubstLDef}} (trm x₁ , proj₂) a x = trm x₁ , proj₂ [ a / x ]
  _[_/_] {{SubstLDef}} (typ x₁ , proj₂) a x = typ x₁ , proj₂ [ a / x ]
  
  _[_/_] {{SubstDefList}} [] a x = []
  _[_/_] {{SubstDefList}} (x₁ ∷ df) a x = x₁ [ a / x ] ∷ df [ a / x ]
  
  _[_/_] {{SubstDefs}} (hd ∷ tl) a x = hd [ a / x ] ∷ tl [ a / x ] 
