(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    Coq library by Arthur Chargueraud. *)

Set Implicit Arguments.

(* Require Import LibLN. *)
Require Import SyntaxAndTactics.
Require Import Metalib.Metatheory.
Require Import Metalib.AssocList.
Require Import LibUtils.

Inductive typ : Set :=
| typ_top : typ
| typ_bot : typ
| typ_sel : avar -> typ_label -> typ
| typ_all : typ -> typ -> typ
| typ_obj : nlist dec -> typ
with
dec : Set :=
(** dec_typ X A B ::= X : A .. B *)
| dec_typ : typ_label -> typ -> typ -> dec
(** dec_trm x T ::= x : T *)
| dec_trm : trm_label -> typ -> dec.

Hint Constructors typ dec : alg_def.

Notation "⊤" := typ_top.
Notation "⊥" := typ_bot.
Notation "x ⋅ T" := (typ_sel x T) (at level 40).
Notation "all( A ); B" := (typ_all A B) (at level 40).

Notation "X ⦂ A ⋯ B" := (dec_typ X A B) (at level 40).
Notation "x ∷ T" := (dec_trm x T) (at level 40).
Notation "μ{ d ; .. ; dn ;; dnn }" :=
  (typ_obj $ (mult d .. (mult dn (single dnn)) ..)) (at level 40).

(* Parameter X : atom. *)
(* Parameter Y : atom. *)
(* Check μ{ X ∷ ⊥ ;; Y ⦂ ⊥ ⋯ ⊤ }. *)

Instance dec_has_label : HasLabel dec :=
  {
    get_label d :=
        match d with
        | l ⦂ _ ⋯ _ => l
        | l ∷ _ => l
        end;
  }.


Inductive trm : Set :=
| trm_var : avar -> trm
| trm_val : val -> trm
| trm_sel : avar -> trm_label -> trm
| trm_app : avar -> avar -> trm
| trm_let : trm -> trm -> trm
with
val : Set :=
| val_new : nlist dec -> nlist def -> val
| val_lambda : typ -> trm -> val
with
def : Set :=
| def_typ : typ_label -> typ -> def
| def_trm : trm_label -> trm -> def.

Hint Constructors trm val def : alg_def.

Notation "'let' x 'in' y" := (trm_let x y) (at level 40).

Notation "A ⦂= B" := (def_typ A B) (at level 40).
Notation "x ⩴ t" := (def_trm x t) (at level 40).

Notation "ν( d ; .. ; dn ;; dnn ){ df ; .. ; dfn ;; dfnn }" :=
  (val_new (mult d .. (mult dn (single dnn)) .. )
           (mult df .. (mult dfn (single dfnn)) .. )) (at level 40).

Notation "λ( T ){ t }" := (val_lambda T t) (at level 40).

Instance def_has_label : HasLabel def :=
  {
    get_label d :=
        match d with
        | l ⦂= _ => l
        | l ⩴ _ => l
        end;
  }.
