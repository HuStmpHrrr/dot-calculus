{-# OPTIONS --safe #-}

module Relation.Binary.Decidability where

import Relation.Binary.Core as RCore

open import Relation.Nullary using (Dec ; yes ; no) public
open import Level

-- | semiautomated proof using agda's instance resolution.
instan : ∀ {a} {A : Set a} {{_ : A}} → A
instan {{x}} = x


-- | decidability should be defined as a type class,
-- such that there is no need to input what is decidable or not.
record Decidable {a b ℓ} {A : Set a} {B : Set b}
                 (_~_ : RCore.REL A B ℓ) : Set (a ⊔ b ⊔ ℓ) where
  field
    dec : ∀ x y → Dec (x ~ y)


open Decidable {{...}} public

-- | convert the functional definition of decidability to
-- the type class one.
decidable : ∀ {a b ℓ} {A : Set a} {B : Set b}
              {_~_ : RCore.REL A B ℓ} →
              RCore.Decidable _~_ →
              Decidable _~_
decidable d = record { dec = d }


-- | we definitely wants a function back to traditional decidability
decide : ∀ {a b ℓ} {A : Set a} {B : Set b}
              {_~_ : RCore.REL A B ℓ} →
              {{_ : Decidable _~_}} →
              RCore.Decidable _~_
decide x y = dec x y


open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open import Function.Equality hiding (setoid)
open import Function.Injection
open import Function.Surjection
open import Function.Bijection


-- now we are about to show two notions of decidability are trivially the same.


module _ {a b ℓ} {A : Set a} {B : Set b}
         (_~_ : RCore.REL A B ℓ) where

  RCoreDec : Setoid _ _
  RCoreDec = setoid (RCore.Decidable _~_)

  RecDec : Setoid _ _
  RecDec = setoid (Decidable _~_)

  ≡decidable≡ : RCoreDec ⟶ RecDec
  ≡decidable≡ = →-to-⟶ {B = RecDec} decidable

  conv-injective : Injective ≡decidable≡
  conv-injective = λ { refl → refl }

  conv-injection : (RCore.Decidable _~_) ↣ (Decidable _~_)
  conv-injection = record
                   { to        = ≡decidable≡
                   ; injective = conv-injective
                   }

  decide′ : Decidable _~_ → RCore.Decidable _~_
  decide′ ev = decide {{ev}}

  ≡decide≡ : RecDec ⟶ RCoreDec
  ≡decide≡ = →-to-⟶ {B = RCoreDec} decide′

  conv-surjective : Surjective ≡decidable≡
  conv-surjective = record
                    { from             = ≡decide≡
                    ; right-inverse-of = λ _ → refl
                    }

  conv-surjection : (RCore.Decidable _~_) ↠ (Decidable _~_)
  conv-surjection = record
                    { to         = ≡decidable≡
                    ; surjective = conv-surjective
                    }

  conv-bijective : Bijective ≡decidable≡
  conv-bijective = record
                   { injective  = conv-injective
                   ; surjective = conv-surjective
                   }

  conv-bijection : Bijection RCoreDec RecDec
  conv-bijection = record
                   { to        = ≡decidable≡
                   ; bijective = conv-bijective
                   }
