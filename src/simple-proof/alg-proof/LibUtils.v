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

Notation "<| d |>" := (single d) (at level 39).

Notation "<| d ; .. ; dn ;; dnn |>" :=
  (mult d .. (mult dn (single dnn)) ..) (at level 39).


Definition led_by {A : Type} (a : A) (nl : nlist A) : Prop :=
  match nl with
  | single x => x = a
  | mult x _ => x = a
  end.

Definition replace_head {A : Type} (a : A) (nl : nlist A) : nlist A :=
  match nl with
  | single _ => single a
  | mult _ xs => mult a xs
  end.

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

Module nlistOps.
  Fixpoint map {A B : Type} (f : A -> B) (l : nlist A) : nlist B :=
    match l with
    | <| x |> => <| f x |>
    | mult x xs => mult (f x) $ map f xs
    end.

  Fixpoint app {A : Type} (l1 l2 : nlist A) : nlist A :=
    match l1 with
    | single x => mult x l2
    | mult x xs => mult x $ app xs l2
    end.
  
  Theorem app_assoc : forall {A} (l1 l2 l3 : nlist A),
      app l1 (app l2 l3) = app (app l1 l2) l3.
  Proof.
    intros A l1.
    induction l1; intros; simpl in *; try f_equal; auto.
  Qed.
End nlistOps.

Notation "l1 +++ l2" := (nlistOps.app l1 l2) (at level 60, right associativity).

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


Class HasLabel (T : Set) :=
  {
    get_label : T -> label
  }.

Definition to_label_assoc {T} {hlb : HasLabel T} :=
 nlist_to_assoc get_label.

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


(* Definition replace_by_key {A : Set} {hlb : HasLabel A} *)
(*            (l : label) (nv : A) (nl : nlist A) : nlist A := *)
(*   nlistOps.map (fun e => if get_label e == l then nv else e) nl. *)


(* Lemma replace_effective : forall {A : Set} {hlb : HasLabel A} l e nv (nl : nlist A), *)
(*     LabelAssocList.binds l e $ to_label_assoc nl -> *)
(*     get_label e = l -> *)
(*     get_label nv = l -> *)
(*     LabelAssocList.binds l nv $ to_label_assoc $ replace_by_key l nv nl. *)
(* Proof. *)
(*   intros. gen e l nv. unfold LabelAssocList.binds. *)
(*   induction nl; intros; simpl in *; destruct_all; subst; try contradiction; *)
(*   try (destruct_eq; [left; trivial | congruence]). *)
(*   destruct_eq. *)
