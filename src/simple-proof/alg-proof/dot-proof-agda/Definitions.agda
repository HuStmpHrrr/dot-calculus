{-# OPTIONS --safe #-}
module Definitions where

open import Data.Nat renaming (ℕ to Nat ; _⊔_ to max)
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

open import ListUtils

record Var : Set where
  constructor var_
  field
    -- |there are countably infinite natural numbers,
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
    infix 10 _⟨_↦_⟩
    field
      _⟨_↦_⟩ : A → Nat → Var → A

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
  constructor decTrm
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
  ⊤     : Typ
  ⊥     : Typ
  _·_   : (x : Avar) → (T : TypLabel) → Typ
  Π[_]_ : (T : Typ) → (U : Typ) → Typ
  μ[_]  : (DS : Decs) → Typ


data Trm : Set
data Val : Set

record DefTyp : Set where
  constructor defTyp
  inductive
  field
    Ty : Typ

record DefTrm : Set where
  constructor defTrm
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
  var_      : Avar → Trm
  val_      : Val → Trm
  _·_       : (x : Avar) → (t : TrmLabel) → Trm
  _!$!_     : (s : Avar) → (t : Avar) → Trm
  llet_iin_ : (s : Trm) → (t : Trm) → Trm

data Val where
  ν[_]⟨_⟩ : (DS : Decs) → (ds : Defs) → Val
  Λ[_]⟨_⟩ : (T : Typ) → (t : Trm) → Val

open CanOpen {{...}} public
open DecTyp public
open DecTrm public

--| open from zero
_⟨0↦_⟩ : ∀ {a} {A : Set a} → A → {{_ : CanOpen A}} → Var → A
a ⟨0↦ v ⟩ = a ⟨ 0 ↦ v ⟩
infix 10 _⟨0↦_⟩

instance
  OpenAvar : CanOpen Avar
  _⟨_↦_⟩ {{OpenAvar}} (b x) n v with x ≟ n
  ... | yes p                   = f v
  ... | no ¬p                   = b n
  _⟨_↦_⟩ {{OpenAvar}} (f x) n v = f x


instance
  OpenTyp     : CanOpen Typ
  OpenDecTyp  : CanOpen DecTyp
  OpenDecTrm  : CanOpen DecTrm
  OpenLDec    : CanOpen LDec
  OpenDecList : CanOpen (List LDec)
  OpenDecs    : CanOpen Decs

  _⟨_↦_⟩ {{OpenTyp}} ⊤ n v                = ⊤
  _⟨_↦_⟩ {{OpenTyp}} ⊥ n v                = ⊥
  _⟨_↦_⟩ {{OpenTyp}} (x · T) n v          = x ⟨ n ↦ v ⟩ · T
  _⟨_↦_⟩ {{OpenTyp}} (Π[ T ] U) n v       = Π[ T ⟨ n ↦ v ⟩ ] U ⟨ suc n ↦ v ⟩
  _⟨_↦_⟩ {{OpenTyp}} μ[ DS ] n v          = μ[ DS ⟨ suc n ↦ v ⟩ ]
  
  _⟨_↦_⟩ {{OpenDecTyp}} (lb ⋯ ub) n v     = lb ⟨ n ↦ v ⟩ ⋯ ub ⟨ n ↦ v ⟩
  
  _⟨_↦_⟩ {{OpenDecTrm}} (decTrm Ttr) n v  = decTrm $ Ttr ⟨ n ↦ v ⟩

  _⟨_↦_⟩ {{OpenLDec}} (trm x , proj₂) n v = trm x , proj₂ ⟨ n ↦ v ⟩
  _⟨_↦_⟩ {{OpenLDec}} (typ x , proj₂) n v = typ x , proj₂ ⟨ n ↦ v ⟩

  _⟨_↦_⟩ {{OpenDecList}} [] n v           = []
  _⟨_↦_⟩ {{OpenDecList}} (x ∷ DS) n v     = x ⟨ n ↦ v ⟩ ∷ DS ⟨ n ↦ v ⟩

  _⟨_↦_⟩ {{OpenDecs}} (hd ∷ tl) n v       = hd ⟨ n ↦ v ⟩ ∷ tl ⟨ n ↦ v ⟩


infix 10 _⟨0↦_⟩ᵗ
_⟨0↦_⟩ᵗ : Typ → Var → Typ
μ[ DS ] ⟨0↦ v ⟩ᵗ = μ[ DS ⟨0↦ v ⟩ ]
T ⟨0↦ v ⟩ᵗ = T ⟨0↦ v ⟩


instance
  OpenTrm     : CanOpen Trm
  OpenVal     : CanOpen Val
  OpenDefTyp  : CanOpen DefTyp
  OpenDefTrm  : CanOpen DefTrm
  OpenLDef    : CanOpen LDef
  OpenDefList : CanOpen (List LDef)
  OpenDefs    : CanOpen Defs

  _⟨_↦_⟩ {{OpenTrm}} (var x) n v          = var x ⟨ n ↦ v ⟩
  _⟨_↦_⟩ {{OpenTrm}} (val x) n v          = val x ⟨ n ↦ v ⟩
  _⟨_↦_⟩ {{OpenTrm}} (x · x₁) n v         = x ⟨ n ↦ v ⟩ · x₁
  _⟨_↦_⟩ {{OpenTrm}} (x !$! x₁) n v       = x ⟨ n ↦ v ⟩ !$! x₁ ⟨ n ↦ v ⟩
  _⟨_↦_⟩ {{OpenTrm}} (llet t iin t₁) n v  = llet t ⟨ n ↦ v ⟩ iin t₁ ⟨ suc n ↦ v ⟩

  _⟨_↦_⟩ {{OpenVal}} ν[ DS ]⟨ ds ⟩ n v    = ν[ DS ⟨ n ↦ v ⟩ ]⟨ ds ⟨ n ↦ v ⟩ ⟩
  _⟨_↦_⟩ {{OpenVal}} Λ[ T ]⟨ t ⟩ n v      = Λ[ T ⟨ n ↦ v ⟩ ]⟨ t ⟨ n ↦ v ⟩ ⟩
  
  _⟨_↦_⟩ {{OpenDefTyp}} (defTyp Ty) n v   = defTyp $ Ty ⟨ n ↦ v ⟩
  
  _⟨_↦_⟩ {{OpenDefTrm}} (defTrm tr) n v   = defTrm $ tr ⟨ n ↦ v ⟩
  
  _⟨_↦_⟩ {{OpenLDef}} (trm x , proj₂) n v = trm x , proj₂ ⟨ n ↦ v ⟩
  _⟨_↦_⟩ {{OpenLDef}} (typ x , proj₂) n v = typ x , proj₂ ⟨ n ↦ v ⟩
  
  _⟨_↦_⟩ {{OpenDefList}} [] n v           = []
  _⟨_↦_⟩ {{OpenDefList}} (x ∷ df) n v     = x ⟨ n ↦ v ⟩ ∷ df ⟨ n ↦ v ⟩
  
  _⟨_↦_⟩ {{OpenDefs}} (hd ∷ tl) n v       = hd ⟨ n ↦ v ⟩ ∷ tl ⟨ n ↦ v ⟩
  

infix 10 _⟨0↦_⟩ᵛ
_⟨0↦_⟩ᵛ : Val → Var → Val
ν[ DS ]⟨ df ⟩ ⟨0↦ v ⟩ᵛ = ν[ DS ⟨0↦ v ⟩ ]⟨ df ⟨0↦ v ⟩ ⟩
l@(Λ[ _ ]⟨ _ ⟩) ⟨0↦ v ⟩ᵛ = l ⟨0↦ v ⟩

open HasFv {{...}} public

instance
  FvAvar : HasFv Avar
  fv {{FvAvar}} (b x) = []
  fv {{FvAvar}} (f x) = List.[ x ]

instance
  FvTyp     : HasFv Typ
  FvDecTyp  : HasFv DecTyp
  FvDecTrm  : HasFv DecTrm
  FvLDec    : HasFv LDec
  FvDecList : HasFv (List LDec)
  FvDecs    : HasFv Decs

  fv {{FvTyp}} ⊤                = []
  fv {{FvTyp}} ⊥                = []
  fv {{FvTyp}} (x · T)          = fv x
  fv {{FvTyp}} (Π[ T ] U)       = fv T ++ fv U
  fv {{FvTyp}} μ[ DS ]          = fv DS
  
  fv {{FvDecTyp}} (lb₁ ⋯ ub₁)   = fv lb₁ ++ fv ub₁
  
  fv {{FvDecTrm}} (decTrm Ttr)  = fv Ttr
  
  fv {{FvLDec}} (trm x , proj₂) = fv proj₂
  fv {{FvLDec}} (typ x , proj₂) = fv proj₂
  
  fv {{FvDecList}} []           = []
  fv {{FvDecList}} (x ∷ t)      = fv x ++ fv t
  
  fv {{FvDecs}} (hd ∷ tl)       = fv hd ++ fv tl


instance
  FvTrm     : HasFv Trm
  FvVal     : HasFv Val
  FvDefTyp  : HasFv DefTyp
  FvDefTrm  : HasFv DefTrm
  FvLDef    : HasFv LDef
  FvDefList : HasFv (List LDef)
  FvDefs    : HasFv Defs

  fv {{FvTrm}} (var x)          = fv x
  fv {{FvTrm}} (val x)          = fv x
  fv {{FvTrm}} (x · _)          = fv x
  fv {{FvTrm}} (x !$! x₁)       = fv x ++ fv x₁
  fv {{FvTrm}} (llet t iin t₁)  = fv t ++ fv t₁
  
  fv {{FvVal}} ν[ DS ]⟨ ds ⟩    = fv DS ++ fv ds
  fv {{FvVal}} Λ[ T ]⟨ t ⟩      = fv T ++ fv t
  
  fv {{FvDefTyp}} (defTyp Ty)   = fv Ty
  fv {{FvDefTrm}} (defTrm tr)   = fv tr
  
  fv {{FvLDef}} (trm x , proj₄) = fv proj₄
  fv {{FvLDef}} (typ x , proj₄) = fv proj₄
  
  fv {{FvDefList}} []           = []
  fv {{FvDefList}} (x ∷ t)      = fv x ++ fv t
  
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
  SubstTyp     : CanSubst Typ
  SubstDecTyp  : CanSubst DecTyp
  SubstDecTrm  : CanSubst DecTrm
  SubstLDec    : CanSubst LDec
  SubstDecList : CanSubst (List LDec)
  SubstDecs    : CanSubst Decs

  _[_/_] {{SubstTyp}} ⊤ a x                 = ⊤
  _[_/_] {{SubstTyp}} ⊥ a x                 = ⊥
  _[_/_] {{SubstTyp}} (x₁ · T) a x          = x₁ [ a / x ] · T
  _[_/_] {{SubstTyp}} (Π[ T ] U) a x        = Π[ T [ a / x ] ] U [ a / x ]
  _[_/_] {{SubstTyp}} μ[ DS ] a x           = μ[ DS [ a / x ] ]
  
  _[_/_] {{SubstDecTyp}} (lb₁ ⋯ ub₁) a x    = lb₁ [ a / x ] ⋯ ub₁ [ a / x ]
  _[_/_] {{SubstDecTrm}} (decTrm Ttr) a x   = decTrm $ Ttr [ a / x ]
    
  _[_/_] {{SubstLDec}} (trm x₁ , proj₄) a x = trm x₁ , proj₄ [ a / x ]
  _[_/_] {{SubstLDec}} (typ x₁ , proj₄) a x = typ x₁ , proj₄ [ a / x ]
  
  _[_/_] {{SubstDecList}} [] a x            = []
  _[_/_] {{SubstDecList}} (x₁ ∷ t) a x      = x₁ [ a / x ] ∷ t [ a / x ]
  
  _[_/_] {{SubstDecs}} (head₁ ∷ tail₁) a x  = head₁ [ a / x ] ∷ tail₁ [ a / x ]
  

instance
  SubstTrm     : CanSubst Trm
  SubstVal     : CanSubst Val
  SubstDefTyp  : CanSubst DefTyp
  SubstDefTrm  : CanSubst DefTrm
  SubstLDef    : CanSubst LDef
  SubstDefList : CanSubst (List LDef)
  SubstDefs    : CanSubst Defs

  _[_/_] {{SubstTrm}} (var x₁) a x          = var x₁ [ a / x ]
  _[_/_] {{SubstTrm}} (val x₁) a x          = val x₁ [ a / x ]
  _[_/_] {{SubstTrm}} (x₁ · t) a x          = x₁ [ a / x ] · t
  _[_/_] {{SubstTrm}} (t !$! s) a x         = t [ a / x ] !$! s [ a / x ]
  _[_/_] {{SubstTrm}} (llet t iin t₁) a x   = llet t [ a / x ] iin t₁ [ a / x ]

  _[_/_] {{SubstVal}} ν[ DS ]⟨ ds ⟩ a x     = ν[ DS [ a / x ] ]⟨ ds [ a / x ] ⟩
  _[_/_] {{SubstVal}} Λ[ T ]⟨ t ⟩ a x       = Λ[ T [ a / x ] ]⟨ t [ a / x ] ⟩
  
  _[_/_] {{SubstDefTyp}} (defTyp Ty) a x    = defTyp $ Ty [ a / x ]
  
  _[_/_] {{SubstDefTrm}} (defTrm tr) a x    = defTrm $ tr [ a / x ]
  
  _[_/_] {{SubstLDef}} (trm x₁ , proj₂) a x = trm x₁ , proj₂ [ a / x ]
  _[_/_] {{SubstLDef}} (typ x₁ , proj₂) a x = typ x₁ , proj₂ [ a / x ]
  
  _[_/_] {{SubstDefList}} [] a x            = []
  _[_/_] {{SubstDefList}} (x₁ ∷ df) a x     = x₁ [ a / x ] ∷ df [ a / x ]
  
  _[_/_] {{SubstDefs}} (hd ∷ tl) a x        = hd [ a / x ] ∷ tl [ a / x ] 

infix 6 _~_
_~_ : ∀ {a b}{A : Set a}{B : A → Set b} → (x : A) → B x → List (Σ A B)
x ~ y = List.[ x , y ]

infix 3 _⊢_⦂_  _⊢_<⦂_  _⊢_::_  _⊢[_::_]
data _⊢_⦂_     : Env → Trm → Typ → Set
data _⊢_<⦂_    : Env → Typ → Typ → Set
data _⊢_::_    : Env → LDef → LDec → Set
data _⊢[_::_]⁻ : Env → List LDef → List LDec → Set

record _⊢[_::_] (Γ : Env) (ds : Defs) (DS : Decs) : Set where
  constructor ⊢[::]
  inductive
  open List⁺.List⁺
  field
    ty-head : Γ ⊢ head ds :: head DS
    ty-tail : Γ ⊢[ tail ds :: tail DS ]⁻

data _⊢_⦂_ where
  ty-var : ∀ {Γ x T} → x ↦ T ∈ Γ → Γ ⊢ var f x ⦂ T
  ty-Π-I : ∀ {L Γ T t U} →
                (∀ x → x ∉ L → x ~ T ++ Γ ⊢ t ⟨0↦ x ⟩ ⦂ U ⟨0↦ x ⟩) →
                Γ ⊢ val Λ[ T ]⟨ t ⟩ ⦂ Π[ T ] U
  ty-Π-E : ∀ {Γ x y S T} → Γ ⊢ var x ⦂ Π[ S ] T →
                Γ ⊢ var y ⦂ S →
                Γ ⊢ x !$! y ⦂ T
  ty-μ-I : ∀ {L Γ ds DS} →
                (∀ x → x ∉ L → x ~ μ[ DS ] ⟨0↦ x ⟩ᵗ ++ Γ ⊢[ ds :: DS ]) →
                Γ ⊢ val ν[ DS ]⟨ ds ⟩ ⦂ μ[ DS ]
  ty-μ-E : ∀ {Γ x a DS T} → Γ ⊢ var x ⦂ μ[ DS ] →
                trm a ↦ decTrm T ∈⁺ DS →
                Γ ⊢ x · a ⦂ T
  ty-let : ∀ {L Γ t u T U} →
                Γ ⊢ t ⦂ T →
                (∀ x → x ∉ L → x ~ T ++ Γ ⊢ u ⟨0↦ x ⟩ ⦂ U) →
                Γ ⊢ llet t iin u ⦂ U
  ty-<⦂  : ∀ {Γ t T U} →
                Γ ⊢ t ⦂ T →
                Γ ⊢ T <⦂ U →
                Γ ⊢ t ⦂ U

data _⊢_::_ where
  ty-dec-typ : ∀ {Γ A T} → Γ ⊢ typ A , defTyp T :: typ A , T ⋯ T
  ty-dec-trm : ∀ {Γ a t T} → Γ ⊢ t ⦂ T →
                 Γ ⊢ trm a , defTrm t :: trm a , decTrm T

data _⊢[_::_]⁻ where
  ty-empty : ∀ {Γ} → Γ ⊢[ [] :: [] ]⁻
  ty-∷     : ∀ {Γ d D ds DS} → Γ ⊢ d :: D → Γ ⊢[ ds :: DS ]⁻ → Γ ⊢[ d ∷ ds :: D ∷ DS ]⁻


data _⊢_<⦂_ where
  <⦂-⊤       : ∀ {Γ T} → Γ ⊢ T <⦂ ⊤
  ⊥-<⦂       : ∀ {Γ T} → Γ ⊢ ⊥ <⦂ T
  <⦂-refl    : ∀ {Γ T} → Γ ⊢ T <⦂ T
  <⦂-trans   : ∀ {Γ S T U} → Γ ⊢ S <⦂ T → Γ ⊢ T <⦂ U → Γ ⊢ S <⦂ U
  <⦂-Π       : ∀ {L Γ S₁ T₁ S₂ T₂} →
                 Γ ⊢ S₂ <⦂ S₁ →
                 (∀ x → x ∉ L → x ~ S₂ ++ Γ ⊢ T₁ ⟨0↦ x ⟩ <⦂ T₂ ⟨0↦ x ⟩) →
                 Γ ⊢ Π[ S₁ ] T₁ <⦂ Π[ S₂ ] T₂
  <⦂-μ-trm   : ∀ {L Γ a T DS₁ DS₂ U} →
                 (∀ x → x ∉ L →
                    x ~ μ[ DS₁ ++⁺′ (trm a , decTrm T) ∷ DS₂ ] ⟨0↦ x ⟩ᵗ ++ Γ ⊢ T <⦂ U) →
                 Γ ⊢ μ[ DS₁ ++⁺′ (trm a , decTrm T) ∷ DS₂ ]
                   <⦂ μ[ DS₁ ++⁺′ (trm a , decTrm U) ∷ DS₂ ]
  <⦂-μ-typ   : ∀ {L Γ A DS₁ DS₂ S₁ T₁ S₂ T₂} →
                 (∀ x → x ∉ L →
                    x ~ μ[ DS₁ ++⁺′ (typ A , S₁ ⋯ T₁) ∷ DS₂ ] ⟨0↦ x ⟩ᵗ ++ Γ ⊢ S₂ <⦂ S₁) →
                 (∀ x → x ∉ L →
                    x ~ μ[ DS₁ ++⁺′ (typ A , S₁ ⋯ T₁) ∷ DS₂ ] ⟨0↦ x ⟩ᵗ ++ Γ ⊢ T₁ <⦂ T₂) →
                 Γ ⊢ μ[ DS₁ ++⁺′ (typ A , S₁ ⋯ T₁) ∷ DS₂ ]
                   <⦂ μ[ DS₁ ++⁺′ (typ A , S₂ ⋯ T₂) ∷ DS₂ ]
  <⦂-μ-drop₁ : ∀ {Γ DS₁ DS₂} → Γ ⊢ μ[ DS₁ ⁺++⁺ DS₂ ] <⦂ μ[ DS₂ ]
  <⦂-μ-drop₂ : ∀ {Γ DS₁ DS₂} → Γ ⊢ μ[ DS₁ ⁺++⁺ DS₂ ] <⦂ μ[ DS₁ ]
  <⦂-μ-merge : ∀ {Γ DS DS₁ DS₂} →
                 Γ ⊢ μ[ DS ] <⦂ μ[ DS₁ ] →
                 Γ ⊢ μ[ DS ] <⦂ μ[ DS₂ ] →
                 Γ ⊢ μ[ DS ] <⦂ μ[ DS₁ ⁺++⁺ DS₂ ]
  <⦂-μ-sel₁  : ∀ {Γ x A S T DS} →
                 Γ ⊢ var x ⦂ μ[ DS ] →
                 typ A ↦ S ⋯ T ∈⁺ DS →
                 Γ ⊢ S <⦂ x · A
  <⦂-μ-sel₂  : ∀ {Γ x A S T DS} →
                 Γ ⊢ var x ⦂ μ[ DS ] →
                 typ A ↦ S ⋯ T ∈⁺ DS →
                 Γ ⊢ x · A <⦂ T
