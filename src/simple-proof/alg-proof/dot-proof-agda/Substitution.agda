{-# OPTIONS --safe #-}

module Substitution where

open import Data.Empty using (⊥-elim)
open import Data.Nat

open import Data.Product
open import Definitions
open import Data.List
open import Data.List.NonEmpty
open import Data.List.Containment
open import Data.List.Containment.Properties

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Decidability

open import Function


record OpenFreshInj (T : Set) {{FvT : HasFv T}} {{OpT : CanOpen T}} : Set where
  field
    open-fresh-injection :
      ∀ {z} (t₁ t₂ : T) k → z ∉ fv t₁ → z ∉ fv t₂ →
        t₁ ⟨ k ↦ z ⟩ ≡ t₂ ⟨ k ↦ z ⟩ →
        t₁ ≡ t₂

open OpenFreshInj {{...}} public

instance
  OfjAvar : OpenFreshInj Avar

  open-fresh-injection {{OfjAvar}} {z}   (b x) (b x₁) k  _ _ eq with x ≟ k | x₁ ≟ k
  open-fresh-injection {{OfjAvar}} {z}   (b x) (b .x) .x _ _ eq | yes refl | yes refl = refl
  open-fresh-injection {{OfjAvar}} {z}   (b x) (b x₁) .x _ _ () | yes refl | no ¬p
  open-fresh-injection {{OfjAvar}} {z}   (b x) (b x₁) k  _ _ () | no ¬p    | yes p
  open-fresh-injection {{OfjAvar}} {z}   (b x) (b x₁) k  _ _ eq | no ¬p    | no ¬p₁   = eq
  open-fresh-injection {{OfjAvar}} {z}   (b x) (f x₁) k  _ _ eq with x ≟ k
  open-fresh-injection {{OfjAvar}} {.x₁} (b x) (f x₁) .x _ z∉f₂ refl | yes refl       = ⊥-elim (z∉f₂ $ found [])
  open-fresh-injection {{OfjAvar}} {z}   (b x) (f x₁) k  _ _ eq      | no ¬p          = eq
  open-fresh-injection {{OfjAvar}} {z}   (f x) (b x₁) k  _ _ eq with x₁ ≟ k
  open-fresh-injection {{OfjAvar}} {.x}  (f x) (b x₁) k z∉f₁ _ refl  | yes p          = ⊥-elim (z∉f₁ (found []))
  open-fresh-injection {{OfjAvar}} {z}   (f x) (b x₁) k _ _ eq       | no ¬p          = eq
  open-fresh-injection {{OfjAvar}} {z}   (f x) (f x₁) k _ _ eq                        = eq

  OfjTyp     : OpenFreshInj Typ
  OfjDecTyp  : OpenFreshInj DecTyp
  OfjDecTrm  : OpenFreshInj DecTrm
  OfjLDec    : OpenFreshInj LDec
  OfjDecList : OpenFreshInj (List LDec)
  OfjDecs    : OpenFreshInj Decs


  open-fresh-injection {{OfjTyp}} {z} ⊤            ⊤            _ _ _ refl = refl
  open-fresh-injection {{OfjTyp}} {z} ⊤            ⊥            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} ⊤            (x · T)      _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} ⊤            (Π[ t₂ ] t₃) _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} ⊤            (μ[ DS ])    _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} ⊥            ⊤            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} ⊥            ⊥            _ _ _ refl = refl
  open-fresh-injection {{OfjTyp}} {z} ⊥            (x · T)      _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} ⊥            (Π[ t₂ ] t₃) _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} ⊥            (μ[ DS ])    _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (x · T)      ⊤            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (x · T)      ⊥            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (x · T)      (x₁ · T₁)    k ∉₁ ∉₂ eq
                       with open-fresh-injection x x₁ k ∉₁ ∉₂
  ...                     | repl
                       with x ⟨ k ↦ z ⟩
                          | x₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjTyp}} {z} (x · T)      (x₁ · .T)    k q w refl
                          | repl | y₁ | .y₁ rewrite repl refl              = refl
  open-fresh-injection {{OfjTyp}} {z} (x · T)      (Π[ t₂ ] t₃) _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (x · T)      (μ[ DS ])    _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (Π[ t₁ ] t₂) ⊤            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (Π[ t₁ ] t₂) ⊥            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (Π[ t₁ ] t₂) (x · T)      _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (Π[ t₁ ] t₂) (Π[ t₃ ] t₄) k ∉₁ ∉₂ eq
                       with open-fresh-injection t₁ t₃ k
                              (∉-reduceˡ (fv t₂) ∉₁) (∉-reduceˡ (fv t₄) ∉₂)
                          | open-fresh-injection t₂ t₄ (suc k)
                              (∉-reduceʳ (fv t₁) ∉₁) (∉-reduceʳ (fv t₃) ∉₂)
  ...                     | inj₁ | inj₂
                       with t₁ ⟨ k ↦ z ⟩
                          | t₂ ⟨ suc k ↦ z ⟩
                          | t₃ ⟨ k ↦ z ⟩
                          | t₄ ⟨ suc k ↦ z ⟩
  open-fresh-injection {{OfjTyp}} {z} (Π[ t₁ ] t₂) (Π[ t₃ ] t₄) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂
                          | t′₁ | t′₂ | .t′₁ | .t′₂
                          rewrite inj₁ refl | inj₂ refl                    = refl
  open-fresh-injection {{OfjTyp}} {z} (Π[ t₁ ] t₂) (μ[ DS ])    _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (μ[ DS ])    ⊤            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (μ[ DS ])    ⊥            _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (μ[ DS ])    (x · T)      _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (μ[ DS ])    (Π[ t₂ ] t₃) _ _ _ ()
  open-fresh-injection {{OfjTyp}} {z} (μ[ DS ])    (μ[ DS₁ ])   k ∉₁ ∉₂ eq
                       with open-fresh-injection DS DS₁ (suc k) ∉₁ ∉₂
  ...                     | inj
                       with DS ⟨ suc k ↦ z ⟩
                          | DS₁ ⟨ suc k ↦ z ⟩
  open-fresh-injection {{OfjTyp}} {z} (μ[ DS ])    (μ[ DS₁ ])   k ∉₁ ∉₂ refl
                          | inj | DS′ | .DS′ rewrite inj refl              = refl
  

  open-fresh-injection {{OfjDecTyp}} {z} (lb₁ ⋯ ub₁) (lb₂ ⋯ ub₂) k ∉₁ ∉₂ eq
                       with open-fresh-injection lb₁ lb₂ k
                              (∉-reduceˡ (fv ub₁) ∉₁) (∉-reduceˡ (fv ub₂) ∉₂)
                          | open-fresh-injection ub₁ ub₂ k
                              (∉-reduceʳ (fv lb₁) ∉₁) (∉-reduceʳ (fv lb₂) ∉₂)
  ...                     | inj₁ | inj₂
                       with lb₁ ⟨ k ↦ z ⟩
                          | ub₁ ⟨ k ↦ z ⟩
                          | lb₂ ⟨ k ↦ z ⟩
                          | ub₂ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDecTyp}} {z} (lb₁ ⋯ ub₁) (lb₂ ⋯ ub₂) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂
                          | lb₁′ | ub₁′ | .lb₁′ | .ub₁′
                          rewrite inj₁ refl | inj₂ refl = refl


  open-fresh-injection {{OfjDecTrm}} {z} (decTrm Ttr₁) (decTrm Ttr₂) k ∉₁ ∉₂ eq
                       with open-fresh-injection Ttr₁ Ttr₂ k ∉₁ ∉₂
  ...                     | inj
                       with Ttr₁ ⟨ k ↦ z ⟩
                          | Ttr₂ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDecTrm}} {z} (decTrm Ttr₁) (decTrm Ttr₂) k ∉₁ ∉₂ refl
                          | inj | Ttr₁′ | .Ttr₁′ rewrite inj refl = refl


  open-fresh-injection {{OfjLDec}} {z} (trm x , dec₁) (trm x₁ , dec₂) k ∉₁ ∉₂ eq
                         with open-fresh-injection dec₁ dec₂ k ∉₁ ∉₂
  ...                       | inj
                         with dec₁ ⟨ k ↦ z ⟩
                            | dec₂ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjLDec}} {z} (trm x , dec₁) (trm .x , dec₂) k ∉₁ ∉₂ refl
                            | inj | dec₁′ | .dec₁′ rewrite inj refl = refl
  open-fresh-injection {{OfjLDec}} {z} (trm x , dec₁) (typ x₁ , dec₂) k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjLDec}} {z} (typ x , dec₁) (trm x₁ , dec₂) k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjLDec}} {z} (typ x , dec₁) (typ x₁ , dec₂) k ∉₁ ∉₂ eq
                         with open-fresh-injection dec₁ dec₂ k ∉₁ ∉₂
  ...                       | inj
                         with dec₁ ⟨ k ↦ z ⟩
                            | dec₂ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjLDec}} {z} (typ x , dec₁) (typ .x , dec₂) k ∉₁ ∉₂ refl
                            | inj | dec₁′ | .dec₁′ rewrite inj refl = refl


  open-fresh-injection {{OfjDecList}} {z} [] [] k ∉₁ ∉₂ eq = refl
  open-fresh-injection {{OfjDecList}} {z} [] (x ∷ t1) k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjDecList}} {z} (x ∷ t) [] k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjDecList}} {z} (x ∷ t) (x₁ ∷ t₁) k ∉₁ ∉₂ eq
                       with open-fresh-injection x x₁ k
                              (∉-reduceˡ (fv t) ∉₁) (∉-reduceˡ (fv t₁) ∉₂)
                          | open-fresh-injection t t₁ k
                              (∉-reduceʳ (fv x) ∉₁) (∉-reduceʳ (fv x₁) ∉₂)
  ...                     | inj₁ | inj₂
                       with x ⟨ k ↦ z ⟩
                          | t ⟨ k ↦ z ⟩
                          | x₁ ⟨ k ↦ z ⟩
                          | t₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDecList}} {z} (x ∷ t) (x₁ ∷ t₁) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | x′ | t′ | .x′ | .t′
                          rewrite inj₁ refl | inj₂ refl       = refl
  

  open-fresh-injection {{OfjDecs}} {z} (h₁ ∷ t₁) (h₂ ∷ t₂) k ∉₁ ∉₂ eq
                       with open-fresh-injection h₁ h₂ k
                              (∉-reduceˡ (fv t₁) ∉₁) (∉-reduceˡ (fv t₂) ∉₂)
                          | open-fresh-injection t₁ t₂ k
                              (∉-reduceʳ (fv h₁) ∉₁) (∉-reduceʳ (fv h₂) ∉₂)
  ...                     | inj₁ | inj₂
                       with h₁ ⟨ k ↦ z ⟩
                          | t₁ ⟨ k ↦ z ⟩
                          | h₂ ⟨ k ↦ z ⟩
                          | t₂ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDecs}} {z} (h₁ ∷ t₁) (h₂ ∷ t₂) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | h₁′ | t₁′ | .h₁′ | .t₁′
                          rewrite inj₁ refl | inj₂ refl = refl

  OfjTrm     : OpenFreshInj Trm
  OfjVal     : OpenFreshInj Val
  OfjDefTyp  : OpenFreshInj DefTyp
  OfjDefTrm  : OpenFreshInj DefTrm
  OfjLDef    : OpenFreshInj LDef
  OfjDefList : OpenFreshInj (List LDef)
  OfjDefs    : OpenFreshInj Defs


  open-fresh-injection {{OfjTrm}} {z} (var x)          (var x₁)         k ∉₁ ∉₂ eq
                       with open-fresh-injection x x₁ k ∉₁ ∉₂
  ...                     | inj
                       with x ⟨ k ↦ z ⟩
                          | x₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjTrm}} {z} (var x) (var x₁) k ∉₁ ∉₂ refl
                          | inj | x′ | .x′ rewrite inj refl = refl
  open-fresh-injection {{OfjTrm}} {z} (var x)          (val x₁)         k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (var x)          (x₁ · t)         k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (var x)          (s !$! t)        k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (var x)          (llet t₂ iin t₃) k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (val x)          (var x₁)         k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (val x)          (val x₁)         k ∉₁ ∉₂ eq
                       with open-fresh-injection x x₁ k ∉₁ ∉₂
  ...                     | inj
                       with x ⟨ k ↦ z ⟩
                          | x₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjTrm}} {z} (val x) (val x₁) k ∉₁ ∉₂ refl
                          | inj | x′ | .x′ rewrite inj refl = refl
  open-fresh-injection {{OfjTrm}} {z} (val x)          (x₁ · t)         k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (val x)          (s !$! t)        k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (val x)          (llet t₂ iin t₃) k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (x · t)          (var x₁)         k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (x · t)          (val x₁)         k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (x · t)          (x₁ · t₁)        k ∉₁ ∉₂ eq
                       with open-fresh-injection x x₁ k ∉₁ ∉₂
  ...                     | inj
                       with x ⟨ k ↦ z ⟩
                          | x₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjTrm}} {z} (x · t) (x₁ · .t) k ∉₁ ∉₂ refl
                          | inj | x′ | .x′ rewrite inj refl = refl
  open-fresh-injection {{OfjTrm}} {z} (x · t)          (s !$! t₁)       k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (x · t)          (llet t₂ iin t₃) k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (s !$! t)        (var x)          k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (s !$! t)        (val x)          k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (s !$! t)        (x · t₁)         k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (s !$! t)        (s₁ !$! t₁)      k ∉₁ ∉₂ eq
                       with open-fresh-injection s s₁ k (∉-reduceˡ _ ∉₁) (∉-reduceˡ _ ∉₂)
                          | open-fresh-injection t t₁ k (∉-reduceʳ (fv s) ∉₁) (∉-reduceʳ (fv s₁) ∉₂)
  ...                     | inj₁ | inj₂
                       with s ⟨ k ↦ z ⟩
                          | t ⟨ k ↦ z ⟩
                          | s₁ ⟨ k ↦ z ⟩
                          | t₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjTrm}} {z} (s !$! t) (s₁ !$! t₁) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | s′ | t′ | .s′ | .t′
                       rewrite inj₁ refl | inj₂ refl        = refl
  open-fresh-injection {{OfjTrm}} {z} (s !$! t)        (llet t₂ iin t₃) k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (llet t₁ iin t₂) (var x)          k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (llet t₁ iin t₂) (val x)          k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (llet t₁ iin t₂) (x · t)          k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (llet t₁ iin t₂) (s !$! t)        k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjTrm}} {z} (llet t₁ iin t₂) (llet t₃ iin t₄) k ∉₁ ∉₂ eq
                       with open-fresh-injection t₁ t₃ k (∉-reduceˡ _ ∉₁) (∉-reduceˡ _ ∉₂)
                          | open-fresh-injection t₂ t₄ (suc k)
                              (∉-reduceʳ (fv t₁) ∉₁) (∉-reduceʳ (fv t₃) ∉₂)
  ...                     | inj₁ | inj₂
                       with t₁ ⟨ k ↦ z ⟩
                          | t₂ ⟨ suc k ↦ z ⟩
                          | t₃ ⟨ k ↦ z ⟩
                          | t₄ ⟨ suc k ↦ z ⟩
  open-fresh-injection {{OfjTrm}} {z} (llet t₁ iin t₂) (llet t₃ iin t₄) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | t₁′ | t₂′ | .t₁′ | .t₂′
                          rewrite inj₁ refl | inj₂ refl     = refl


  open-fresh-injection {{OfjVal}} {z} ν[ DS ]⟨ ds ⟩ ν[ DS₁ ]⟨ ds₁ ⟩ k ∉₁ ∉₂ eq
                       with open-fresh-injection DS DS₁ (suc k) (∉-reduceˡ _ ∉₁) (∉-reduceˡ _ ∉₂)
                          | open-fresh-injection ds ds₁ (suc k)
                              (∉-reduceʳ (fv DS) ∉₁) (∉-reduceʳ (fv DS₁) ∉₂)
  ...                     | inj₁ | inj₂
                       with DS ⟨ suc k ↦ z ⟩
                          | DS₁ ⟨ suc k ↦ z ⟩
                          | ds ⟨ suc k ↦ z ⟩
                          | ds₁ ⟨ suc k ↦ z ⟩
  open-fresh-injection {{OfjVal}} {z} ν[ DS ]⟨ ds ⟩ ν[ DS₁ ]⟨ ds₁ ⟩ k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | DS′ | .DS′ | ds′ | .ds′
                          rewrite inj₁ refl | inj₂ refl = refl
  open-fresh-injection {{OfjVal}} {z} ν[ DS ]⟨ ds ⟩ Λ[ T ]⟨ t ⟩     k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjVal}} {z} Λ[ T ]⟨ t ⟩   ν[ DS ]⟨ ds ⟩   k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjVal}} {z} Λ[ T ]⟨ t ⟩   Λ[ T₁ ]⟨ t₁ ⟩   k ∉₁ ∉₂ eq
                       with open-fresh-injection T T₁ k (∉-reduceˡ _ ∉₁) (∉-reduceˡ _ ∉₂)
                          | open-fresh-injection t t₁ (suc k)
                           (∉-reduceʳ (fv T) ∉₁) (∉-reduceʳ (fv T₁) ∉₂)
  ...                     | inj₁ | inj₂
                       with T ⟨ k ↦ z ⟩
                          | T₁ ⟨ k ↦ z ⟩
                          | t ⟨ suc k ↦ z ⟩
                          | t₁ ⟨ suc k ↦ z ⟩
  open-fresh-injection {{OfjVal}} {z} Λ[ T ]⟨ t ⟩ Λ[ T₁ ]⟨ t₁ ⟩ k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | T′ | .T′ | t′ | .t′
                          rewrite inj₁ refl | inj₂ refl = refl


  open-fresh-injection {{OfjDefTyp}} {z} (defTyp Ty) (defTyp Ty₁) k ∉₁ ∉₂ eq
                       with open-fresh-injection Ty Ty₁ k ∉₁ ∉₂
  ...                     | inj
                       with Ty ⟨ k ↦ z ⟩
                          | Ty₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDefTyp}} {z} (defTyp Ty) (defTyp Ty₁) k ∉₁ ∉₂ refl
                          | inj | Ty′ | .Ty′
                          rewrite inj refl = refl


  open-fresh-injection {{OfjDefTrm}} {z} (defTrm tr) (defTrm tr₁) k ∉₁ ∉₂ eq
                       with open-fresh-injection tr tr₁ k ∉₁ ∉₂
  ...                     | inj
                       with tr ⟨ k ↦ z ⟩
                          | tr₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDefTrm}} {z} (defTrm tr) (defTrm tr₁) k ∉₁ ∉₂ refl
                          | inj | tr′ | .tr′
                          rewrite inj refl = refl


  open-fresh-injection {{OfjLDef}} {z} (trm x , tr) (trm x₁ , tr₁) k ∉₁ ∉₂ eq
                       with open-fresh-injection tr tr₁ k ∉₁ ∉₂
  ...                     | inj
                       with tr ⟨ k ↦ z ⟩
                          | tr₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjLDef}} {z} (trm x , tr) (trm .x , tr₁) k ∉₁ ∉₂ refl
                          | inJ | tr′ | .tr′
                          rewrite inj refl = refl
  open-fresh-injection {{OfjLDef}} {z} (trm x , tr) (typ x₁ , Ty)  k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjLDef}} {z} (typ x , Ty) (trm x₁ , tr)  k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjLDef}} {z} (typ x , Ty) (typ x₁ , Ty₁) k ∉₁ ∉₂ eq
                       with open-fresh-injection Ty Ty₁ k ∉₁ ∉₂
  ...                     | inj
                       with Ty ⟨ k ↦ z ⟩
                          | Ty₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjLDef}} {z} (typ x , Ty) (typ .x , Ty₁) k ∉₁ ∉₂ refl
                          | inj | Ty′ | .Ty′
                          rewrite inj refl = refl


  open-fresh-injection {{OfjDefList}} {z} []      []        k ∉₁ ∉₂ refl = refl
  open-fresh-injection {{OfjDefList}} {z} []      (x ∷ t₁)  k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjDefList}} {z} (x ∷ t) []        k ∉₁ ∉₂ ()
  open-fresh-injection {{OfjDefList}} {z} (x ∷ t) (x₁ ∷ t₁) k ∉₁ ∉₂ eq
                       with open-fresh-injection x x₁ k (∉-reduceˡ _ ∉₁) (∉-reduceˡ _ ∉₂)
                          | open-fresh-injection t t₁ k
                           (∉-reduceʳ (fv x) ∉₁) (∉-reduceʳ (fv x₁) ∉₂)
  ...                     | inj₁ | inj₂
                       with x ⟨ k ↦ z ⟩
                          | x₁ ⟨ k ↦ z ⟩
                          | t ⟨ k ↦ z ⟩
                          | t₁ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDefList}} {z} (x ∷ t) (x₁ ∷ t₁) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | x′ | .x′ | t′ | .t′
                          rewrite inj₁ refl | inj₂ refl                  = refl


  open-fresh-injection {{OfjDefs}} {z} (h₁ ∷ t₁) (h₂ ∷ t₂) k ∉₁ ∉₂ eq
                       with open-fresh-injection h₁ h₂ k
                              (∉-reduceˡ _ ∉₁) (∉-reduceˡ _ ∉₂)
                          | open-fresh-injection t₁ t₂ k
                              (∉-reduceʳ (fv h₁) ∉₁) (∉-reduceʳ (fv h₂) ∉₂)
  ...                     | inj₁ | inj₂
                       with h₁ ⟨ k ↦ z ⟩
                          | t₁ ⟨ k ↦ z ⟩
                          | h₂ ⟨ k ↦ z ⟩
                          | t₂ ⟨ k ↦ z ⟩
  open-fresh-injection {{OfjDefs}} {z} (h₁ ∷ t₁) (h₂ ∷ t₂) k ∉₁ ∉₂ refl
                          | inj₁ | inj₂ | h₁′ | t₁′ | .h₁′ | .t₁′
                       rewrite inj₁ refl | inj₂ refl = refl
