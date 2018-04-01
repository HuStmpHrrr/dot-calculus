module ListUtils where

open import Data.List
open import Data.List.NonEmpty
open import Data.Empty
open import Data.Unit using (⊤ ; tt)

open import Data.Product
open import Function

open import Relation.Nullary

open import Relation.Binary.Core using (_⇒_ ; Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import Data.List.Properties
open import Data.Nat.Properties
import Data.List.NonEmpty.Properties as Neℙ

open import Level


module _ {a} {A : Set a} where
  not-empty : List A → Set
  not-empty []      = ⊥
  not-empty (_ ∷ _) = ⊤

  not-empty-relax : (l1 l l2 : List A) → not-empty l → not-empty $ l1 ++ l ++ l2
  not-empty-relax [] [] l2 ()
  not-empty-relax [] (x ∷ l) l2 ev = tt
  not-empty-relax (x ∷ l1) l l2 ev = tt

  infix 4 _∈_
  data _∈_ (e : A) : List A → Set a where
    skip  : ∀ {l} h → e ∈ l → e ∈ h ∷ l
    found : ∀ l → e ∈ e ∷ l

  dec-∈ : ∀ {dec : Decidable {A = A} _≡_} → Decidable _∈_
  dec-∈ e [] = no (λ ())
  dec-∈ {dec} e (x ∷ l) with dec e x
  dec-∈ {dec} e (x ∷ l) | yes p rewrite p = yes (found l)
  dec-∈ {dec} e (x ∷ l) | no ¬p with dec-∈ {dec} e l
  dec-∈ {dec} e (x ∷ l) | no ¬p | yes p   = yes (skip x p)
  dec-∈ {dec} e (x ∷ l) | no ¬p | no ¬p₁  = no λ {
      (skip .x t) → ¬p₁ t
    ; (found .l)  → ¬p refl
    }

  ∈⇒not-empty : {e : A} {l : List A} → e ∈ l → not-empty l
  ∈⇒not-empty (skip h c) = tt
  ∈⇒not-empty (found l)  = tt

  infix 4 _∉_
  _∉_ : A → List A → Set a
  e ∉ l = ¬ (e ∈ l)

  ∈-witness : ∀ l₁ x l₂ → x ∈ l₁ ++ x ∷ l₂
  ∈-witness [] _ l₂        = found l₂
  ∈-witness (x ∷ l₁) x′ l₂ = skip x $ ∈-witness l₁ x′ l₂

  data uniq : List A → Set a where
    empty : uniq []
    grow  : ∀ {h l} → h ∉ l → uniq l → uniq $ h ∷ l


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


mapVal : ∀ {a b}{A : Set a}{B : A → Set b}{C : A → Set b} →
         (f : (x : A) → B x → C x) →
         List (Σ A B) → List (Σ A C)
mapVal f [] = []
mapVal f ((proj₁ , proj₂) ∷ l) = (proj₁ , f proj₁ proj₂) ∷ mapVal f l


-- about nonempty lists
module _ {a} {A : Set a} where

  NeList⇒List⁺ : NeList A → List⁺ A
  NeList⇒List⁺ ([] , ())
  NeList⇒List⁺ (x ∷ tl , tt) = x ∷ tl

  List⁺⇒NeList : List⁺ A → NeList A
  List⁺⇒NeList (head₁ ∷ tail₁) = head₁ ∷ tail₁ , tt

  data DesList⁺ {a}(A : Set a) : Set a where
    _∷[] : (hd : A) → DesList⁺ A
    _∷_ : (hd : A) → (tl : List⁺ A) → DesList⁺ A
    
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


  dec-∈⁺ : ∀ {dec : Decidable {A = A} _≡_} → Decidable _∈⁺_
  dec-∈⁺ {dec} e l with dec-∈ {dec = dec} e $ toList l
  dec-∈⁺ {dec} e l | yes p = yes $ wrap p
  dec-∈⁺ {dec} e l | no ¬p = no λ { (wrap ev) → ¬p ev }
  
  ∈⁺⇒∈ : ∀ {e l} → e ∈⁺ l → e ∈ toList l
  ∈⁺⇒∈ (wrap ev) = ev

  infixr 5 _++⁺′_
  _++⁺′_ : List A → List⁺ A → List⁺ A
  [] ++⁺′ l₂       = l₂
  (x ∷ l₁) ++⁺′ l₂ = x ∷ l₁ ++ toList l₂

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
    where ∈⁺wit : x ∈⁺ l₁ ++⁺′ x ∷ l₂
          ∈⁺wit = ∈⁺-witness l₁ x l₂
          wit-conv : x ∈⁺ l₁ ++⁺′ x ∷ l₂ → x ∈⁺ l₁ ++⁺ x ∷ l₂
          wit-conv ev rewrite ++⁺′≡++⁺ l₁ $ x ∷ l₂ = ev


module _ {a b}{A : Set a}{B : A → Set b} where
  private 
    a⊔b : Level
    a⊔b = a ⊔ b

  _↦_∈⁺_ : (x : A) → B x → List⁺ (Σ A B) → Set (a⊔b)
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
