module Data.List.Containment.Core where

open import Data.List
open import Data.List.NonEmpty
open import Data.Empty
open import Data.Unit using (⊤ ; tt)

open import Data.Product
open import Function

open import Relation.Nullary

-- open import Relation.Binary.Core using (_⇒_ ; Decidable)
open import Relation.Binary.Decidability
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (Decidable)

open import Data.List.Properties
open import Data.Nat.Properties
import Data.List.NonEmpty.Properties as Neℙ

open import Level

open Decidable {{...}} public

module _ {a} {A : Set a} where
  not-empty : List A → Set
  not-empty []      = ⊥
  not-empty (_ ∷ _) = ⊤

  not-empty-relax : (l1 l l2 : List A) → not-empty l → not-empty $ l1 ++ l ++ l2
  not-empty-relax [] [] l2 ()
  not-empty-relax [] (x ∷ l) l2 ev = tt
  not-empty-relax (x ∷ l1) l l2 ev = tt

  infix 4 _∈_  _∉_ _∈?_  _∈??_
  data _∈_ (e : A) : List A → Set a where
    instance
      skip  : ∀ {l} h → e ∈ l → e ∈ h ∷ l
      found : ∀ l     → e ∈ e ∷ l

  _∉_ : A → List A → Set a
  e ∉ l = ¬ (e ∈ l)

  instance
    ∈-dec : ∀ {{_ : Decidable {A = A} _≡_}} → Decidable _∈_
    ∈-dec {{d}} = record
                    { dec = ∈-dec′
                    } where
      ∈-dec′ : (e : A) → (l : List A) → Dec (e ∈ l)
      ∈-dec′ e []                        = no (λ ())
      ∈-dec′ e (x ∷ l) with dec {{d}} e x
      ∈-dec′ e (x ∷ l) | yes p rewrite p = yes (found l)
      ∈-dec′ e (x ∷ l) | no ¬p with ∈-dec′ e l
      ∈-dec′ e (x ∷ l) | no ¬p | yes p   = yes (skip x p)
      ∈-dec′ e (x ∷ l) | no ¬p | no ¬p₁  = no λ {
          (skip .x t) → ¬p₁ t
        ; (found .l)  → ¬p refl
        }

  _∈?_ : ∀ {{_ : Decidable {A = A} _∈_}} → (e : A) → (l : List A) → Dec (e ∈ l)
  e ∈? l = dec e l

  _∈??_ : ∀ {{_ : Decidable {A = A} _≡_}} → (e : A) → (l : List A) → Dec (e ∈ l)
  _∈??_ e l = e ∈? l

  ∈⇒not-empty : {e : A} {l : List A} → e ∈ l → not-empty l
  ∈⇒not-empty (skip h c) = tt
  ∈⇒not-empty (found l)  = tt

  ∈-witness : ∀ l₁ x l₂ → x ∈ l₁ ++ x ∷ l₂
  ∈-witness [] _ l₂        = found l₂
  ∈-witness (x ∷ l₁) x′ l₂ = skip x $ ∈-witness l₁ x′ l₂

  data uniq : List A → Set a where
    instance
      empty : uniq []
      grow  : ∀ {h l} → h ∉ l → uniq l → uniq $ h ∷ l

  infix 4 _⊆_  _⊈_  _⊆?_  _≋_  _!≋_  _≋?_  _⊂_  _⊄_  _⊂?_
  -- subset relation
  data _⊆_ : List A → List A → Set a where
    instance
      ∅    : ∀ l → [] ⊆ l
      grow : ∀ h {t l} → (h∈l : h ∈ l) → (t⊆l : t ⊆ l) → h ∷ t ⊆ l

  _⊈_ : List A → List A → Set a
  l₁ ⊈ l₂ = ¬ (l₁ ⊆ l₂)

  _≋_ : List A → List A → Set a
  l₁ ≋ l₂ = l₁ ⊆ l₂ × l₂ ⊆ l₁

  _!≋_ : List A → List A → Set a
  l₁ !≋ l₂ = ¬ (l₁ ≋ l₂)

  -- |strictly set order
  _⊂_ : List A → List A → Set a
  l₁ ⊂ l₂ = l₁ ⊆ l₂ × l₂ ⊈ l₁
  
  _⊄_ : List A → List A → Set a
  l₁ ⊄ l₂ = ¬ (l₁ ⊂ l₂)

  instance
    ⊆-dec : ∀ {{_ : Decidable {A = A} _∈_}} → Decidable _⊆_
    ⊆-dec = record
            { dec = ⊆-dec′
            } where
      ⊆-dec′ : ∀ (x y : List A) → Dec (x ⊆ y)
      ⊆-dec′ [] l′              = yes (∅ l′)
      ⊆-dec′ (x ∷ l) l′ with x ∈? l′
      ... | yes p with ⊆-dec′ l l′
      ...            | yes p₁   = yes (grow x p p₁)
      ...            | no ¬p    = no λ{ (grow _ h∈l x₁) → ¬p x₁ }
      ⊆-dec′ (x ∷ l) l′ | no ¬p = no λ { (grow _ h∈l r) → ¬p h∈l }

  _⊆?_ : ∀ {{_ : Decidable _⊆_}} (x y : List A) → Dec (x ⊆ y)
  l₁ ⊆? l₂ = dec l₁ l₂

  instance
    ≋-dec : ∀ {{_ : Decidable {A = A} _∈_}} → Decidable _≋_
    ≋-dec = record
            { dec = ≋-dec′
            } where
      ≋-dec′ : (x y : List A) → Dec (x ≋ y)
      ≋-dec′ x y with x ⊆? y | y ⊆? x
      ≋-dec′ x y | yes x⊆y | yes y⊆x = yes (x⊆y , y⊆x)
      ≋-dec′ x y | yes x⊆y | no y⊈x  = no (λ z → y⊈x (proj₂ z))
      ≋-dec′ x y | no x⊈y  | yes y⊆x = no (λ z → x⊈y (proj₁ z))
      ≋-dec′ x y | no x⊈y  | no y⊈x  = no (λ z → y⊈x (proj₂ z))

  _≋?_ : ∀ {{_ : Decidable _≋_}} → (x y : List A) → Dec (x ≋ y)
  x ≋? y = dec x y

  instance
    ⊂-dec : ∀ {{_ : Decidable {A = A} _∈_}} → Decidable _⊂_
    ⊂-dec = record
            { dec = ⊂-dec′
            } where
      ⊂-dec′ : (x y : List A) → Dec (x ⊂ y)
      ⊂-dec′ x y with x ⊆? y | y ⊆? x
      ⊂-dec′ x y | yes x⊆y | yes y⊆x = no (λ z → proj₂ z y⊆x)
      ⊂-dec′ x y | yes x⊆y | no y⊈x  = yes (x⊆y , y⊈x)
      ⊂-dec′ x y | no x⊈y  | yes y⊆x = no (λ z → proj₂ z y⊆x)
      ⊂-dec′ x y | no x⊈y  | no y⊈x  = no (λ z → x⊈y (proj₁ z))

  _⊂?_ : ∀ {{_ : Decidable _⊂_}} → (x y : List A) → Dec (x ⊂ y)
  _⊂?_ = dec


module _ {a b}{A : Set a}{B : A → Set b} where
  private
    a⊔b : Level
    a⊔b = a ⊔ b

  _↦_∈_ : (x : A) → B x → List (Σ A B) → Set a⊔b
  k ↦ v ∈ M = (k , v) ∈ M

  infix 7 _[_↦_]ᴸ_  _[_↦_]
  _[_↦_] : ∀ M (k : A) {v : B k} (nv : B k) → k ↦ v ∈ M →
             Σ (List (Σ A B)) (λ M′ → k ↦ nv ∈ M′)
  ((.h ∷ l) [ k ↦ nv ]) (skip h ev) with (l [ k ↦ nv ]) ev
  ... | M' , ev'                        = h ∷ M' , skip h ev'
  (.((k , _) ∷ l) [ k ↦ nv ]) (found l) = (k , nv) ∷ l , found l

  _[_↦_]ᴸ_ : ∀ M (k : A) {v : B k} (nv : B k) → k ↦ v ∈ M → List (Σ A B)
  M [ k ↦ nv ]ᴸ ev = proj₁ $ (M [ k ↦ nv ]) ev

  ↦∈-witness : ∀ M₁ M₂ (k : A) (v nv : B k) →
                 ((M₁ ++ (k , v) ∷ M₂) [ k ↦ nv ]ᴸ
                 (∈-witness M₁ (k , v) M₂)) ≡ M₁ ++ (k , nv) ∷ M₂
  ↦∈-witness [] _ _ _ _             = refl
  ↦∈-witness (x ∷ M₁) M₂ k v nv
    rewrite ↦∈-witness M₁ M₂ k v nv = refl


NeList : ∀ {a} (A : Set a) → Set a
NeList A = Σ (List A) not-empty


-- about nonempty lists
module _ {a} {A : Set a} where

  NeList⇒List⁺ : NeList A → List⁺ A
  NeList⇒List⁺ ([] , ())
  NeList⇒List⁺ (x ∷ tl , tt) = x ∷ tl

  List⁺⇒NeList : List⁺ A → NeList A
  List⁺⇒NeList (head₁ ∷ tail₁) = head₁ ∷ tail₁ , tt

  data DesList⁺ {a}(A : Set a) : Set a where
    _∷[] : (hd : A) → DesList⁺ A
    _∷_  : (hd : A) → (tl : List⁺ A) → DesList⁺ A

  des-view⁺ : ∀ {a}{A : Set a} → List⁺ A → DesList⁺ A
  des-view⁺ (head₁ ∷ [])        = head₁ ∷[]
  des-view⁺ (head₁ ∷ x ∷ tail₁) = head₁ ∷ x ∷ tail₁

  infix 4 _∈⁺_  _∉⁺_
  record _∈⁺_ (e : A) (l : List⁺ A) : Set a where
    constructor wrap
    field
      ev : e ∈ toList l

  _∉⁺_ : A → List⁺ A → Set a
  e ∉⁺ l = ¬ (e ∈⁺ l)


  instance
    ∈⁺-dec : ∀ {{_ : Decidable {A = A} _≡_}} → Decidable _∈⁺_
    ∈⁺-dec = record
               { dec = ∈⁺-dec′
               } where
      ∈⁺-dec′ : ∀ (x : A) (y : List⁺ A) → Dec (x ∈⁺ y)
      ∈⁺-dec′ e l with dec e $ toList l
      ∈⁺-dec′ e l | yes p = yes $ wrap p
      ∈⁺-dec′ e l | no ¬p = no λ { (wrap ev) → ¬p ev }
  
  ∈⁺⇒∈ : ∀ {e l} → e ∈⁺ l → e ∈ toList l
  ∈⁺⇒∈ (wrap ev) = ev

  infixr 5 _++⁺′_
  _++⁺′_ : List A → List⁺ A → List⁺ A
  [] ++⁺′ l₂       = l₂
  (x ∷ l₁) ++⁺′ l₂ = x ∷ l₁ ++ toList l₂


  infix 4 _⊆⁺_  _⊈⁺_  _⁺⊆⁺_  _⁺⊈⁺_
  record _⊆⁺_ (l : List A) (l′ : List⁺ A) : Set a where
    field
      l⊆l′ : l ⊆ toList l′

  _⊈⁺_ : List A → List⁺ A → Set a
  l ⊈⁺ l′ = ¬ (l ⊆⁺ l′)

  record _⁺⊆⁺_ (l : List⁺ A) (l′ : List⁺ A) : Set a where
    field
      l⊆l′ : toList l ⊆ toList l′

  _⁺⊈⁺_ : List⁺ A → List⁺ A → Set a
  l ⁺⊈⁺ l′ = ¬ (l ⁺⊆⁺ l′)

  record uniq⁺ (l : List⁺ A) : Set a where
    field
      uq : uniq $ toList l

  ++⁺≡++⁺′ : ∀ l₁ l₂ → l₁ ++⁺ l₂ ≡ l₁ ++⁺′ l₂
  ++⁺≡++⁺′ [] l₂ = refl
  ++⁺≡++⁺′ (x ∷ l₁) l₂ rewrite ++⁺≡++⁺′ l₁ l₂ with l₁
  ... | []       = refl
  ... | x′ ∷ l₁′ = refl

  -- |for the fun of it
  ++⁺′≡++⁺ : ∀ l₁ l₂ → l₁ ++⁺′ l₂ ≡ l₁ ++⁺ l₂
  ++⁺′≡++⁺ [] l₂ = refl
  ++⁺′≡++⁺ (x ∷ l₁) l₂ rewrite sym $ ++⁺′≡++⁺ l₁ l₂ with l₁
  ... | []       = refl
  ... | _ ∷ _    = refl

  toList-++⁺ : ∀ (l₁ : List A) l₂ → (toList $ l₁ ++⁺ l₂) ≡ l₁ ++ toList l₂
  toList-++⁺ [] _                                 = refl
  toList-++⁺ (x ∷ l₁) l₂ rewrite toList-++⁺ l₁ l₂ = refl

  ∈⁺-witness : ∀ l₁ x l₂ → x ∈⁺ l₁ ++⁺′ x ∷ l₂
  ∈⁺-witness [] x l₂         = wrap $ ∈-witness [] x l₂
  ∈⁺-witness l₁@(_ ∷ _) x l₂ = wrap $ ∈-witness l₁ x l₂

  ∈⁺-witness₂ : ∀ l₁ x l₂ → x ∈⁺ l₁ ++⁺ x ∷ l₂
  ∈⁺-witness₂ l₁ x l₂ = wit-conv ∈⁺wit
    where ∈⁺wit    : x ∈⁺ l₁ ++⁺′ x ∷ l₂
          ∈⁺wit = ∈⁺-witness l₁ x l₂
          wit-conv : x ∈⁺ l₁ ++⁺′ x ∷ l₂ → x ∈⁺ l₁ ++⁺ x ∷ l₂
          wit-conv ev rewrite ++⁺′≡++⁺ l₁ $ x ∷ l₂ = ev


module _ {a b}{A : Set a}{B : A → Set b} where
  private 
    a⊔b : Level
    a⊔b = a ⊔ b

  _↦_∈⁺_ : (x : A) → B x → List⁺ (Σ A B) → Set a⊔b
  k ↦ v ∈⁺ M = (k , v) ∈⁺ M

  infix 7 _[_↦_]⁺ _[_↦_]⁺ᴸ_
  _[_↦_]⁺ : ∀ M (k : A) {v : B k} (nv : B k) → k ↦ v ∈⁺ M →
              Σ (List⁺ (Σ A B)) (λ M′ → k ↦ nv ∈⁺ M′)
  ((hd ∷ tl) [ k ↦ nv ]⁺) (wrap ev) with ((hd ∷ tl) [ k ↦ nv ]) ev
  ... | [] , ()
  ... | x ∷ l , ev′ = x ∷ l , wrap ev′

  _[_↦_]⁺ᴸ_ : ∀ M (k : A) {v : B k} (nv : B k) → k ↦ v ∈⁺ M → List⁺ (Σ A B)
  M [ k ↦ nv ]⁺ᴸ ev = proj₁ $ (M [ k ↦ nv ]⁺) ev

  ↦∈⁺-toList : ∀ M₁ M₂ (k : A) (v nv : B k) →
                 toList ((M₁ ++⁺′ (k , v) ∷ M₂) [ k ↦ nv ]⁺ᴸ (∈⁺-witness M₁ (k , v) M₂))
                 ≡ (M₁ ++ (k , v) ∷ M₂) [ k ↦ nv ]ᴸ (∈-witness M₁ (k , v) M₂)
  ↦∈⁺-toList [] M₂ k v nv       = refl
  ↦∈⁺-toList (x ∷ M₁) M₂ k v nv = refl


  ↦∈⁺-witness : ∀ M₁ M₂ (k : A) (v nv : B k) →
                  ((M₁ ++⁺′ (k , v) ∷ M₂) [ k ↦ nv ]⁺ᴸ (∈⁺-witness M₁ (k , v) M₂))
                  ≡ M₁ ++⁺′ (k , nv) ∷ M₂
  ↦∈⁺-witness [] M₂ k v nv           = refl
  ↦∈⁺-witness (x ∷ M₁) M₂ k v nv
    rewrite ↦∈⁺-witness M₁ M₂ k v nv
          | ↦∈-witness  M₁ M₂ k v nv = refl

  -- ↦∈⁺-witness₂ : ∀ M₁ M₂ (k : A) (v nv : B k) →
  --                 ((M₁ ++⁺ (k , v) ∷ M₂) [ k ↦ nv ]⁺ᴸ (∈⁺-witness₂ M₁ (k , v) M₂))
  --                 ≡ M₁ ++⁺ (k , nv) ∷ M₂
  -- ↦∈⁺-witness₂ [] M₂ k v nv = refl
  -- ↦∈⁺-witness₂ (x ∷ M₁) M₂ k v nv rewrite ++⁺≡++⁺′ M₁ (k , v) M₂ = {!!}
  --   where wit₁ = ↦∈⁺-witness M₁ M₂ k v nv
