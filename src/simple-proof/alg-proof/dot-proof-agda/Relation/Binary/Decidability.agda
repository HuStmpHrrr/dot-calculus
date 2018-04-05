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
                 ( _~_ : RCore.REL A B ℓ) : Set (a ⊔ b ⊔ ℓ) where
  field
    dec : ∀ x y → Dec (x ~ y)


-- | convert the functional definition of decidability to
-- the type class one.
decidable : ∀ {a b ℓ} {A : Set a} {B : Set b}
              {_~_ : RCore.REL A B ℓ} →
              RCore.Decidable _~_ →
              Decidable _~_
decidable d = record { dec = d }
