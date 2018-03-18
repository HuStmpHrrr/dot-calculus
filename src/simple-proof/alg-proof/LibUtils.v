Set Implicit Arguments.

Require Import SyntaxAndTactics.
Require Import Metalib.Metatheory.
Require Import Metalib.AssocList.

Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.

(** PRIMITIVES *)

Definition not_empty {A : Type} (l : list A) : Prop :=
  match l with
  | nil => False
  | cons _ _ => True
  end.

Inductive list_pred {A B : Type} (pred : (A * B) -> Prop) : list (A * B) -> Prop :=
| pred_nil : list_pred pred nil
| pred_cons : forall x xs, pred x -> list_pred pred xs -> list_pred pred $ x :: xs.
Hint Constructors list_pred : alg_def.


(** Following defines labels *)

Inductive typ_label : Set := typ_lab (_ : nat).

Hint Constructors typ_label : alg_def.
Coercion typ_lab : nat >-> typ_label.

Inductive trm_label : Set := trm_lab (_ : nat).

Hint Constructors trm_label : alg_def.
Coercion trm_lab : nat >-> trm_label.

Inductive label : Set :=
| label_typ : typ_label -> label
| label_trm : trm_label -> label.

Hint Constructors label : alg_def.

Coercion label_typ : typ_label >-> label.
Coercion label_trm : trm_label >-> label.


(** Following code assigns abilities to reason about assoc list
    keyed by labels. *)
Module Type EqDecidableType <: UsualDecidableType.
  Parameter t : Set.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  
  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.
End EqDecidableType.

Module Label <: EqDecidableType.
  Definition t := label.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros. destruct x as [x | x]; destruct y as [y | y];
              destruct x, y;
    match goal with
    | [ |- context[?c (_ ?x) = ?c (_ ?y)]] =>
      destruct (Nat.eq_dec x y); [left | right]
    | _ => right
    end; congruence.
  Defined.
  
  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.
End Label.

Module LabelSetImpl : FSetExtra.WSfun Label :=
  FSetExtra.Make Label.

Module LabelAssocList := AssocList.Make Label LabelSetImpl.

