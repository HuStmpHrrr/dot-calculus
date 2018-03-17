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


Inductive nlist (A : Type) : Type :=
| single (_ : A)
| mult (_ : A) (_ : nlist A).
Hint Constructors nlist : alg_def.

Fixpoint nlist_to_list {A : Type} (l : nlist A) : list A :=
  match l with
  | single x => x :: nil
  | mult x xs => x :: nlist_to_list xs
  end.

Theorem nlist_to_list_not_empty :
  forall T (l : nlist T),
    not_empty $ nlist_to_list l.
Proof.
  intros. destruct l; simpl in *; apply I.
Qed.


Definition nlist_to_nelist {A : Type} (l : nlist A) : {res | @not_empty A res}.
Proof.
  econstructor. instantiate (1 := nlist_to_list  l).
  apply nlist_to_list_not_empty.
Defined.

Fixpoint nelist_to_nlist' {A : Type}
         (l : list A) (ev : not_empty l) {struct l} : nlist A.
Proof.
  gen l.
  induction l as [| x xs]; intros.
  - contradiction.
  - remember xs as xs'. destruct xs as [| xx xxs].
    + apply single; auto.
    + apply (mult x).
      apply nelist_to_nlist' with (l := xs').
      subst. trivial.
Defined.


Definition nelist_to_nlist {A : Type} (l : { l | @not_empty A l }) : nlist A :=
  match l with
  | exist _ l ev => nelist_to_nlist' l ev
  end.

Coercion nlist_to_list : nlist >-> list.

Definition nlist_to_assoc {T S : Type}
           (getter : T -> S) (ds : nlist T) : list (S * T) :=
  map (fun d => (getter d, d)) ds.
Hint Unfold nlist_to_assoc : nlist.

Lemma extract_sound : forall T S tup l d (getter : T -> S) ds,
    In tup $ nlist_to_assoc getter ds ->
    tup = (l, d) ->
    l = getter d.
Proof.
  intros. gen tup l d. 
  induction ds; intros; simpl in *; destruct_all; subst; try congruence.
  - contradiction.
  - unfold nlist_to_list in H.  eauto.
Qed.


Inductive avar : Set :=
| avar_b : nat -> avar
| avar_f : var -> avar.

Hint Constructors avar : alg_def.

Coercion avar_b : nat >-> avar.
Coercion avar_f : var >-> avar.

Inductive typ_label : Set := typ_lab (_ : nat).

Hint Constructors typ_label : alg_def.
(* Coercion typ_lab : atom >-> typ_label. *)

Inductive trm_label : Set := trm_lab (_ : nat).

Hint Constructors trm_label : alg_def.
(* Coercion trm_lab : atom >-> trm_label. *)

Inductive label : Set :=
| label_typ : typ_label -> label
| label_trm : trm_label -> label.

Hint Constructors label : alg_def.

Coercion label_typ : typ_label >-> label.
Coercion label_trm : trm_label >-> label.


Class HasLabel (T : Set) :=
  {
    get_label : T -> label
  }.

Definition to_label_assoc {T} {hlb : HasLabel T} :=
 nlist_to_assoc get_label.

Module Type EqDecidableType <: UsualDecidableType.
  Parameter t : Set.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  
  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.
End EqDecidableType.

Module Label : EqDecidableType.
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
