Set Implicit Arguments.

Require Import Metalib.Metatheory.
Require Import Metalib.AssocList.

Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.

Require Import Program.Equality.


Notation "f $ x" := ((f) (x)) (at level 68, right associativity, only parsing).

Notation "<[ e1 ; .. ; en ]>" := (cons e1 .. (cons en nil) .. ) (at level 39).

(** Some Tactics *)

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
  | [ ev : _ + { _ } |- _ ] => destruct ev
  end.

Ltac destruct_eq :=
  simpl;
  destruct_notin;
  match goal with
  | [ |- context[if ?x == ?x then _ else _]] =>
    destruct (x == x); [| congruence]
  | [ |- context[if ?x == ?y then _ else _]] =>
    destruct (x == y); [subst |]
  | [ H : context[if ?x == ?x then _ else _] |- _] =>
    destruct (x == x); [| congruence]
  | [ H : context[if ?x == ?y then _ else _] |- _] =>
    destruct (x == y); [subst |]
  end.

Ltac dep_destruct ev :=
  let E := fresh "E" in
  remember ev as E; simpl in E; dependent destruction E.

Ltac pick_fresh_do name tac :=
  let L := gather_atoms in
  let L := beautify_fset L in
  let Fr := fresh "Fr" in
  tac L; try intros name Fr.

Ltac doit from num tac :=
  match from with
  | num =>  idtac
  | _ => tac from; doit constr:(S from) num tac
  end.


Ltac cofinite :=
  let inst := ltac:(fun L =>
                      instantiate (1 := L) ||
                      instantiate (2 := L) ||
                      instantiate (3 := L) ||
                      instantiate (4 := L)) in
  match goal with
  | [  |- forall _, _ `notin` _ -> _ ] =>
    let x := fresh "x" in
    pick_fresh_do x inst
  | [ H : ?x `notin` _ |- _ ] =>
    gen x; cofinite
  end.

Ltac solve_by_invert :=
  match goal with
  | [ H : ?T |- _ ] =>
    match type of T with
    | Prop => solve [inversion H]
    end
  end.


Ltac find_induction term :=
  match goal with
  | [ |- forall _ : ?T, _ ] =>
    let H := fresh "H" in
    intro H;
    match type of H with
    | context[term] =>
      induction H
    | _ => 
      find_induction term
    end
  | [ |- _ ] =>
    fail 1 "cannot find an induction target of " term
  end.

Tactic Notation "induction" "on" constr(term) :=
  find_induction term.

Ltac exvar T tac :=
  let x := fresh "x" in
  evar (x : T);
  let x' := eval unfold x in x in
  clear x; tac x'.

Ltac exexec lem tac :=
  match type of lem with
  | _ /\ _ => exexec constr:(proj1 lem) tac
            || exexec constr:(proj2 lem) tac
  | forall _ : ?T, _ =>
    exvar T ltac:(fun x' =>
      match type of (lem x') with
      | context[_ /\ _] =>
        exexec constr:(lem x') tac
      end)
  | _ => tac lem
  end.

Tactic Notation "exrewrite" constr(lem) :=
  exexec lem ltac:(fun l => rewrite l).

Tactic Notation "eexrewrite" constr(lem) :=
  exexec lem ltac:(fun l => erewrite l).

Tactic Notation "exapply" constr(lem) :=
  exexec lem ltac:(fun l => apply l).

Tactic Notation "eexapply" constr(lem) :=
  exexec lem ltac:(fun l => eapply l).


(** Tactics for list reassociation. *)

Ltac non_dec_list nat_list :=
  let rec scan nlist p :=
      match nlist with
      | nil => idtac
      | ?h :: ?t => match h with context[p] => scan t h end
      end in
  match nat_list with
  | nil => idtac
  | cons ?h ?t => scan t h
  | _ => fail "the given list is not non-decreasing " nat_list
  end.


Ltac reassoc' lst assoc :=
  match type of lst with
  | list ?T =>
    let rec partition l cnt target cb := (* cnt <= target *)
        match cnt with
        | target => cb l (@nil T)
        | _ => match l with
              | ?h :: ?t => partition t (S cnt) target ltac:(fun l' ed => cb l' (h :: ed))
              end
        end in
    let rec scan l cnt ac cb :=
        match ac with
        | nil => cb (l :: nil)
        | ?target :: ?ac' =>
          partition l cnt target
                    ltac:(fun l' p => scan l' target ac' ltac:(fun l' => cb (p :: l')))
        end in
    scan lst 0 assoc ltac:(fun l => l)
  end.


Ltac collect_list apps :=
  let rec col ap cb := match ap with
                       | ?l1 ++ ?l2 => col l2 ltac:(fun l => cb (l1 :: l))
                       | _ => cb (ap :: nil)
                       end in
  col apps ltac:(fun l => l).


Ltac map_list tac lst :=
  match lst with
  | ?h :: ?t => let h' := tac h in
               let t' := map_list tac t in constr:(h' :: t')
  | @nil ?T => constr:(@nil T)
  end.

Ltac app_lists lists :=
  let rec appl l cb :=
      match type of l with
      | list (list ?T) => match l with
                         | ?h :: nil => cb h
                         | ?h :: ?t => appl t ltac:(fun l' => cb (h ++ l'))
                         | _ => cb (@nil (list T))
                         end
      end in
  let rec col l :=
      match type of l with
      | list (list (list ?T)) =>
        match l with
        | ?h :: ?t => let x := appl h ltac:(fun l => l) in
                     let y := col t in constr:(x :: y)
        | _ => constr:(@nil (list T))
        end
      end in
  let rec x := col lists in appl x ltac:(fun l => l).

Ltac try_discharge :=
  try congruence.

(** The skeleton of decision procesure.
 * unfortunately, the undecidability of this language is too complex
 * to handle by tactics that solves purely logical problems. 
 * TODO: see where autorewrite can be applied. *)
Ltac routine_impl prep tac :=
  intros; try cofinite;
  try solve_by_invert;
  prep;
  simpl in *; cbn in *; subst; autounfold;
  fold any not;
  repeat destruct_eq; destruct_all;
  repeat f_equal;
  repeat split;
  tac.

Tactic Notation "routine" "by" tactic(prep)
       "hinted" tactic(tac)
       "at" int(n) := 
  routine_impl prep ltac:(idtac; tac; try assumption; try_discharge; auto n).

Tactic Notation "routine" "by" tactic(prep) "hinted" tactic(tac) :=
  routine by ltac:(idtac; prep) hinted tac at 5.

Tactic Notation "routine" "by" tactic(prep)
       "at" int(n) := 
  routine_impl prep ltac:(idtac; try assumption; try_discharge; auto n).

Tactic Notation "routine" "hinted" tactic(tac)
       "at" int(n) := 
  routine_impl ltac:(idtac)
               ltac:(idtac; tac; try assumption; try_discharge; auto n).

Tactic Notation "routine" "hinted" tactic(tac) :=
  routine by ltac:(idtac) hinted ltac:(idtac; tac).

Tactic Notation "routine" "by" tactic(prep) :=
  routine by ltac:(idtac; prep) at 5.

Tactic Notation "routine" "hinted" tactic(tac) :=
  routine hinted ltac:(idtac; tac) at 5.

Tactic Notation "routine" := routine by ltac:(idtac).

Tactic Notation "eroutine" "by" tactic(prep)
       "hinted" tactic(tac)
       "at" int(n) := 
  routine_impl prep ltac:(idtac; tac; try assumption; try_discharge; eauto n).

Tactic Notation "eroutine" "by" tactic(prep) "hinted" tactic(tac) :=
  eroutine by ltac:(idtac; prep) hinted tac at 5.

Tactic Notation "eroutine" "by" tactic(prep)
       "at" int(n) := 
  routine_impl prep ltac:(idtac; try assumption; try_discharge; eauto n).

Tactic Notation "eroutine" "hinted" tactic(tac)
       "at" int(n) := 
  routine_impl ltac:(idtac)
               ltac:(idtac; tac; try assumption; try_discharge; eauto n).

Tactic Notation "eroutine" "hinted" tactic(tac) :=
  eroutine by ltac:(idtac) hinted ltac:(idtac; tac).

Tactic Notation "eroutine" "by" tactic(prep) :=
  eroutine by ltac:(idtac; prep) at 5.

Tactic Notation "eroutine" "hinted" tactic(tac) :=
  eroutine hinted ltac:(idtac; tac) at 5.

Tactic Notation "eroutine" := eroutine by ltac:(idtac).

(** try to prove a trm by routine, and then place it into context. *)
Tactic Notation "induce" constr(trm) :=
  assert trm by routine.

(** try to prove a trm by induction on ind *)
Tactic Notation "induce" constr(trm) "on" constr(ind) :=
  assert trm by (induction on ind; routine).


Tactic Notation "einduce" constr(trm) :=
  assert trm by eroutine.

Tactic Notation "einduce" constr(trm) "on" constr(ind) :=
  assert trm by (induction on ind; eroutine).


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

Lemma not_empty_relax : forall {A : Type} (l1 l l2 : list A),
    not_empty l -> not_empty $ l1 ++ l ++ l2.
Proof.
  induction l1; intros; invert_not_empty; simpl; trivial.
Qed.

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


(**
 * It's very painful that we will need to deal with two data types that
 * are effectively lists, but we cannot use list directly, because we need
 * to build mutual recursion.
 *)

Class ListIso (elem : Type) (t : Type) :=
  {
    to_list : t -> list elem;
    from_list : list elem -> t;
    from_to_iso : forall (l : t), from_list $ to_list l = l;
    to_from_iso : forall (l : list elem), to_list $ from_list l = l;
    (* Operations *)
    append : t -> t -> t;
    append_sound : forall l1 l2, to_list $ append l1 l2 = to_list l1 ++ to_list l2
  }.

Section ListIsoProps.

  Variable elem : Type.
  Variable t : Type.
  Variable iso : ListIso elem t.
  
  Theorem append_complete :
    forall l1 l2, append (from_list l1) $ from_list l2 = from_list $ l1 ++ l2.
  Proof.
    intros.
    replace (append (from_list l1) $ from_list l2)
      with (from_list $ to_list $ append (from_list l1) $ from_list l2).
    - f_equal. rewrite append_sound. do 2 rewrite to_from_iso.
      auto.
    - rewrite from_to_iso. auto.
  Qed.

End ListIsoProps.
Arguments append_complete {elem t iso}.


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


