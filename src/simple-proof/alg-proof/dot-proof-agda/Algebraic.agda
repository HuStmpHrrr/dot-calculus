module Algebraic where

import Definitions
open import Data.List
open import Data.List.NonEmpty
open import Data.List.Containment
open import Data.Product

open import Relation.Binary

module Typ≊ where
  open Definitions

  infix 4 _≊_
  data _≊_   : Typ → Typ → Set where
    ≊-⊤      : ⊤ ≊ ⊤
    ≊-⊥      : ⊥ ≊ ⊥
    ≊-var    : ∀ {v T} → v · T ≊ v · T
    ≊-tran   : ∀ {T₁ T₂ T₃} → T₁ ≊ T₂ → T₂ ≊ T₃ → T₁ ≊ T₃
    ≊-Π      : ∀ {S₁ T₁ S₂ T₂} →
                 S₁ ≊ S₂ → T₁ ≊ T₂ →
                 Π[ S₁ ] T₁ ≊ Π[ S₂ ] T₂
    ≊-μ-refl : ∀ DS → μ[ DS ] ≊ μ[ DS ]
    ≊-μ-swap : ∀ DS₁ DS₂ → μ[ DS₁ ⁺++⁺ DS₂ ] ≊ μ[ DS₂ ⁺++⁺ DS₁ ]
    ≊-μ-trm  : ∀ DS₁ DS₂ {a T U} →
                 T ≊ U → 
                 μ[ DS₁ ++⁺′ (trm a , decTrm T) ∷ DS₂ ]
                 ≊ μ[ DS₁ ++⁺′ (trm a , decTrm U) ∷ DS₂ ]
    ≊-μ-Typ  : ∀ DS₁ DS₂ {A S₁ T₁ S₂ T₂} →
                 S₁ ≊ S₂ → T₁ ≊ T₂ →
                 μ[ DS₁ ++⁺′ (typ A , S₁ ⋯ T₁) ∷ DS₂ ]
                 ≊ μ[ DS₁ ++⁺′ (typ A , S₂ ⋯ T₂) ∷ DS₂ ]
  
  ≊-refl : Reflexive _≊_
  ≊-refl {⊤}         = ≊-⊤
  ≊-refl {⊥}         = ≊-⊥
  ≊-refl {x · T}     = ≊-var
  ≊-refl {Π[ T ] T₁} = ≊-Π ≊-refl ≊-refl
  ≊-refl {μ[ DS ]}   = ≊-μ-refl DS
  
  ≊-sym : Symmetric _≊_
  ≊-sym ≊-⊤                      = ≊-⊤
  ≊-sym ≊-⊥                      = ≊-⊥
  ≊-sym ≊-var                    = ≊-var
  ≊-sym (≊-tran eq eq₁)          = ≊-tran (≊-sym eq₁) (≊-sym eq)
  ≊-sym (≊-Π eq eq₁)             = ≊-Π (≊-sym eq) (≊-sym eq₁)
  ≊-sym (≊-μ-refl DS)            = ≊-μ-refl DS
  ≊-sym (≊-μ-swap DS₁ DS₂)       = ≊-μ-swap DS₂ DS₁
  ≊-sym (≊-μ-trm DS₁ DS₂ eq)     = ≊-μ-trm DS₁ DS₂ (≊-sym eq)
  ≊-sym (≊-μ-Typ DS₁ DS₂ eq eq₁) = ≊-μ-Typ DS₁ DS₂ (≊-sym eq) (≊-sym eq₁)
  
  
  instance
    ≊-equiv : IsEquivalence _≊_
    ≊-equiv = record
              { refl  = ≊-refl
              ; sym   = ≊-sym
              ; trans = ≊-tran
              }


open Definitions using (Label ; trm ; typ ; Avar ; b_ ; f_ ; TypLabel)
open import Data.List.AssocList


data Type : Set

infix 7 _⋯_
record DecType : Set where
  inductive
  constructor _⋯_
  field
    lb : Type
    ub : Type

record DecTerm : Set where
  constructor decTerm
  inductive
  field
    Ttr : Type

Decr : Label → Set
Decr (trm _) = DecTerm
Decr (typ _) = DecType

LDecr : Set
LDecr = Σ Label Decr

Decrs : Set
Decrs = Map⁺ Label Decr

infix 7 _·_ Π[_]_ μ[_]
infixl 6 _∧_  _∨_

data ConType : Set where
  ⊤     : ConType
  ⊥     : ConType
  Π[_]_ : (T : Type) → (U : Type) → ConType
  μ[_]  : (DS : Decrs) → ConType


data AbsType : Set where
  _·_   : (x : Avar) → (T : TypLabel) → AbsType
  _∧_   : (T S : Type) → AbsType
  _∨_   : (T S : Type) → AbsType


infix 5 conT_ absT_
data Type where
  conT_ : (T : ConType) → Type
  absT_ : (T : AbsType) → Type

-- | syntactical subtyping relation.

-- infix 3 _≲_
-- data _≲_ : Type → Type → Set where

--   ≲-⊤       : ∀ {S} → S ≲ conT ⊤
--   ⊥-≲       : ∀ {S} → conT ⊥ ≲ S
--   ≲-refl    : ∀ S → S ≲ S
--   ≲-trans   : ∀ {S T U} → S ≲ T → T ≲ U → S ≲ U
--   -- Π subtyping
--   ≲-Π       : ∀ {S₁ T₁ S₂ T₂} → S₂ ≲ S₁ → T₁ ≲ T₂ → conT Π[ S₁ ] T₁ ≲ conT Π[ S₂ ] T₂
--   -- μ subtyping
--   ≲-μ-trm   : ∀ {a T DS₁ DS₂ U} →
--                 T ≲ U →
--                 conT μ[ DS₁ ++⁺′ (trm a , decTerm T) ∷ DS₂ ]
--                 ≲ conT μ[ DS₁ ++⁺′ (trm a , decTerm U) ∷ DS₂ ]
--   ≲-μ-typ   : ∀ {A DS₁ DS₂ S₁ T₁ S₂ T₂} →
--                 S₂ ≲ S₁ →
--                 T₁ ≲ T₂ →
--                 conT μ[ DS₁ ++⁺′ (typ A , S₁ ⋯ T₁) ∷ DS₂ ]
--                 ≲ conT μ[ DS₁ ++⁺′ (typ A , S₂ ⋯ T₂) ∷ DS₂ ]
--   -- infimum typing
--   ∧-drop₁   : ∀ {T₁ T₂} → absT T₁ ∧ T₂ ≲ T₂
--   ∧-drop₂   : ∀ {T₁ T₂} → absT T₁ ∧ T₂ ≲ T₁
--   ∧-merge   : ∀ {T T₁ T₂} →
--                 T ≲ T₁ →
--                 T ≲ T₂ →
--                 T ≲ absT T₁ ∧ T₂
--   ≲-∧       : ∀ {S U} → S ≲ U → S ≲ absT S ∧ U
--   -- supremum typing, just dual the previous one.
--   ∨-drop₁   : ∀ {T₁ T₂} → T₂ ≲ absT T₁ ∨ T₂
--   ∨-drop₂   : ∀ {T₁ T₂} → T₁ ≲ absT T₁ ∨ T₂
--   ∨-merge   : ∀ {T T₁ T₂} →
--                 T₁ ≲ T →
--                 T₂ ≲ T →
--                 absT T₁ ∨ T₂ ≲ T
--   ∨-≲       : ∀ {S U} → S ≲ U → absT S ∨ U ≲ U
--   -- joint effect with objects
--   ∧-μ-merge : ∀ {DS₁ DS₂} →
--                 absT (conT μ[ DS₁ ]) ∧ (conT μ[ DS₂ ]) ≲ conT μ[ DS₁ ⁺++⁺ DS₂ ]
--   ∧-μ-split : ∀ {DS₁ DS₂} →
--                 conT μ[ DS₁ ⁺++⁺ DS₂ ] ≲ absT (conT μ[ DS₁ ]) ∧ (conT μ[ DS₂ ])



-- infix 3 _≊_
-- _≊_ : Type → Type → Set
-- S ≊ U = S ≲ U × U ≲ S

-- ≊-refl : Reflexive _≊_
-- ≊-refl {T} = ≲-refl T , ≲-refl T

-- ≊-trans : Transitive _≊_
-- ≊-trans (S≲T , T≲S) (T≲U , U≲T) = ≲-trans S≲T T≲U , ≲-trans U≲T T≲S

-- ≊-sym : Symmetric _≊_
-- ≊-sym (S≲T , T≲S) = T≲S , S≲T

-- instance
--   ≊-equiv : IsEquivalence _≊_
--   ≊-equiv = record { refl = ≊-refl ; sym = ≊-sym ; trans = ≊-trans }


