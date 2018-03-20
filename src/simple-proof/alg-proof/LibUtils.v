Set Implicit Arguments.

Require Import Metalib.Metatheory.
Require Import Metalib.AssocList.

Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.

Require Import Program.Equality.


Notation "f $ x" := ((f) (x)) (at level 68, right associativity, only parsing).

Notation "<[ e1 ; .. ; en ]>" := (cons e1 .. (cons en nil) .. ) (at level 39).

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.


Ltac destruct_all :=
  repeat match goal with
  | [ H : ?X \/ ?Y |- _ ] => destruct H
  | [ H : ?X /\ ?Y |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  | [tup : _ * _ |- _ ] => destruct tup
  | [ ev : { _ } + { _ } |- _ ] => destruct ev
  | [ ev : _ + { _ } |- _ ] => destruct_all ev
  end.

Ltac destruct_eq :=
  simpl;
  destruct_notin;
  match goal with
  | [ |- context[if ?x == ?x then _ else _]] => destruct (x == x); [| congruence]
    | [ |- context[if ?x == ?y then _ else _]] => destruct (x == y); [subst |]
  end.

Ltac equality :=
  simpl in *; try congruence;
  destruct_eq; 
  auto; try congruence.

Ltac dep_destruct ev :=
  let E := fresh "E" in
  remember ev as E; simpl in E; dependent destruction E.

Ltac try_discharge :=
  try (fsetdec || congruence).

Ltac routine :=
  intros; simpl in *; try destruct_eq; destruct_all;
  try solve [repeat f_equal; try_discharge; auto];
  try_discharge; auto.

Ltac eroutine :=
  intros; simpl in *; try destruct_eq; destruct_all;
  try solve [repeat f_equal; try_discharge; auto];
  try_discharge; eauto.

(** PRIMITIVES *)

Definition not_empty {A : Type} (l : list A) : Prop :=
  match l with
  | nil => False
  | cons _ _ => True
  end.
Hint Unfold not_empty.

Ltac invert_not_empty_impl H x xs :=
  match type of H with
  | context[not_empty ?l] =>
    destruct l as [| x xs]; simpl in H; [contradiction | idtac]; clear H
  end.

Tactic Notation "invert_not_empty" hyp(h) ident(x) ident(xs) :=
  invert_not_empty_impl h x xs.

Tactic Notation "invert_not_empty" hyp(h) :=
  let x := fresh "x" in
  let xs := fresh "xs" in
  invert_not_empty h x xs.

Ltac invert_all_not_empty :=
  match goal with
  | [ H : context[not_empty _] |- _ ] => invert_not_empty H; invert_all_not_empty
  | _ => idtac
  end.

Tactic Notation "invert_not_empty" := invert_all_not_empty.

Inductive list_pred {A B : Type} (pred : (A * B) -> Prop) : list (A * B) -> Prop :=
| pred_nil : list_pred pred nil
| pred_cons : forall x xs, pred x -> list_pred pred xs -> list_pred pred $ x :: xs.
Hint Constructors list_pred.

Inductive contains {A B : Type} (k : A) (v : B) : list (A * B) -> Type :=
| con_skip : forall k' v' t, contains k v t -> contains k v $ (k', v') :: t
| con_found : forall t, contains k v $ (k, v) :: t.
Hint Constructors contains.

Arguments con_skip {A B k v}.

Notation "l `contains` k ↦ v" := (contains k v l) (at level 80) : type_scope.


Section Containment.
  Variable A : Type.
  Variable B : Type.  

  Variable k : A.
  Variable v : B.
  
  Lemma contains_is_in : forall l,
      l `contains` k ↦ v -> In (k, v) l.
  Proof.
    intros. induction X; [right | left]; trivial.
  Qed.

  Definition contains_dec (k' : A) (v' : B) (l : list (A * B))
             (ev : (k', v') :: l `contains` k ↦ v) :
    (l `contains` k ↦ v) + {k' = k /\ v = v'}.
  Proof.
    dep_destruct ev; auto.
  Defined.

  Definition contains_neq_follows :
    forall (k' : A) (v' : B) (l : list (A * B))
      (ev : (k', v') :: l `contains` k ↦ v),
      k <> k' -> l `contains` k ↦ v.
  Proof.
    intros. dep_destruct (contains_dec ev); routine.
  Defined.

  Lemma contains_means_not_empty :
    forall l, l `contains` k ↦ v -> not_empty l.
  Proof.
    intros. destruct X; auto.
  Qed.

  Definition containment_relaxation :
    forall l (ev : l `contains` k ↦ v) l1 l2,
      l1 ++ l ++ l2 `contains` k ↦ v.
  Proof.
    induction l1; routine.
    induction ev; routine.
  Defined.

End Containment.
Hint Resolve contains_is_in contains_neq_follows contains_means_not_empty.
Hint Resolve containment_relaxation.


Section Replacement.
  Variable A : Type.
  Variable B : Type.
  Variable k : A.
  Variable nv : B.

  Fixpoint replace_value (v : B) (l : list (A * B))
           (ev : l `contains` k ↦ v) : list (A * B) :=
    match ev with
    | con_skip k' v' t ev' => (k', v') :: @replace_value v t ev'
    | con_found _ _ t => (k, nv) :: t
    end.

  Definition replace_eq :
    forall l v (ev : l `contains` k ↦ v),
      replace_value ev `contains` k ↦ nv.
  Proof.
    induction ev; routine.
  Defined.

  Definition replace_neq :
  forall l (v : B) k' v'
    (ev : l `contains` k ↦ v) (ev' : l `contains` k' ↦ v'),
    k <> k' ->
    (replace_value ev) `contains` k' ↦ v'.
  Proof.
    intros.
    induction ev'; dep_destruct ev; eroutine.
  Defined.

End Replacement.

Hint Resolve replace_eq replace_neq.

Module ReplacementExample.
  Corollary replace_twice_eq :
    forall A B l (k : A) (v : B) nv1 nv2
      (ev : l `contains` k ↦ v),
      In (k, nv2) $ replace_value nv2 (replace_eq nv1 ev).
  Proof.
    intros. auto.
  Qed.
End ReplacementExample.


(*
 * It's very painful that we will need to deal with two data types that
 * are effectively lists, but we cannot use list directly, because we need
 * to build mutual recursion.
 *)

Module Type ListIsomorphism.

  Parameter elem : Type.
  Parameter t : Type.

  Parameter to_list : t -> list elem.
  Parameter from_list : list elem -> t.

  Axiom forth_then_back_iso :
    forall (l : t), from_list $ to_list l = l.
  
  Axiom back_then_forth_iso :
    forall (l : list elem), to_list $ from_list l = l.

  (** OPERATIONS *)
  
  Parameter app : t -> t -> t.

  Axiom app_sound :
    forall l1 l2, to_list $ app l1 l2 = to_list l1 ++ to_list l2.

End ListIsomorphism.

Module ListIsoProps (I : ListIsomorphism).
  Import I.

  Local Hint Resolve forth_then_back_iso back_then_forth_iso.
  
  Theorem exists_to_list :
    forall l, exists lt, to_list lt = l.
  Proof.
    intros. exists (from_list l). auto.
  Qed.

  Theorem exists_from_list :
    forall lt, exists l, from_list l = lt.
  Proof.
    intros. exists (to_list lt). auto.
  Qed.

  Theorem app_complete :
    forall l1 l2, app (from_list l1) $ from_list l2 = from_list $ l1 ++ l2.
  Proof.
    intros.
    replace (app (from_list l1) $ from_list l2)
      with (from_list $ to_list $ app (from_list l1) $ from_list l2).
    - f_equal. rewrite app_sound. do 2 rewrite back_then_forth_iso.
      auto.
    - rewrite forth_then_back_iso. auto.
  Qed.

End ListIsoProps.

(** Following defines labels *)

Inductive typ_label : Set := typ_lab (_ : nat).

Coercion typ_lab : nat >-> typ_label.

Inductive trm_label : Set := trm_lab (_ : nat).

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

Notation lbinds := contains.
Notation luniq := LabelAssocList.uniq.
Notation lmap := LabelAssocList.map.


