Set Implicit Arguments.

Require Import Metalib.Metatheory.
Require Import Metalib.AssocList.

Require Export Coq.Structures.Equalities.
Require Export Coq.Lists.List.

Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.


(** timeout in seconds for some tactic.
 * TODO: we shall not need it. however, metalib provides nondeterministic
 * tactics, which is somewhat difficult to get over with.
 *)
Ltac TIMEOUT := 2.


Notation "f $ x" := ((f) (x)) (at level 68, right associativity, only parsing).

Notation "<[ e1 ; .. ; en ]>" := (cons e1 .. (cons en nil) .. ) (at level 39).

(** Some Tactics *)

(** Util Tactics *)

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.

Tactic Notation "invert" hyp(H1) := inversion H1.
Tactic Notation "invert" hyp(H1) hyp(H2) := invert H1; invert H2.
Tactic Notation "invert" hyp(H1) hyp(H2) hyp(H3) := invert H1 H2; invert H3.
Tactic Notation "invert" hyp(H1) hyp(H2) hyp(H3) hyp(H4) := invert H1 H2 H3; invert H4.

Ltac intro_do tac trm :=
  match goal with
  | [ H : context[trm] |- _ ] => tac H
  | _ => intro; intro_do tac trm
  end.

Tactic Notation "destr" "on" constr(trm) :=
  intro_do ltac:(fun H => destruct H) trm.

Tactic Notation "destr" "on" constr(trm1) constr(trm2) :=
  destr on trm1; destr on trm2.

Tactic Notation "invert" "on" constr(trm) :=
  intro_do ltac:(fun H => invert H) trm.

Tactic Notation "invert" "on" constr(trm1) constr(trm2) :=
  invert trm1; invert trm2.

(** hell of a hack. we try to [eapply H] onto the goal and 
 * if it's successful, then we consider it to be inductive hypothesis,
 * and roll back by using [fail];
 * otherwise, we give a higher failure level to break it through. *)
Ltac guess_is_ind_hyp H :=
  try (tryif eapply H then fail else fail 1).

Ltac find_dup_hyp tac non :=
  match goal with
  | [ H : ?X, H' : ?X |- _ ] =>
    lazymatch type of X with
    | Prop => tac H H' X
    | _ => idtac
    end
  | _ => non
  end.

Ltac fail_at_if_dup n :=
  find_dup_hyp ltac:(fun H H' X => fail n "dup hypothesis" H "and" H' ":" X)
                      ltac:(idtac).

Ltac fail_if_dup := fail_at_if_dup ltac:(1).

Ltac clear_dups :=
  repeat find_dup_hyp ltac:(fun H H' _ => clear H || clear H')
                             ltac:(idtac).

Ltac clear_tauto_eq :=
  repeat match goal with [ H : ?X = ?X |- _ ] => clear H end.

Ltac different t1 t2 :=
  lazymatch t1 with
  | t2 => fail
  | _ => idtac
  end.

Tactic Notation "pose" hyp(H) "apply" uconstr(trm) :=
  pose proof H; apply trm in H.

Tactic Notation "pose" hyp(H) "eapply" uconstr(trm) :=
  pose proof H; eapply trm in H.

Ltac dup_eq :=
  clear_tauto_eq;
  lazymatch goal with
  | [ _ : ?X = ?Y, _ : ?Y = ?X |- _ ] => fail
  | [ _ : ?X = ?Y |- ?Y = ?X ] => fail
  | _ => idtac
  end.

Ltac invert_eq H :=
  invert H; subst; clear_tauto_eq; clear_dups.

Ltac progressive_inversion :=
  match goal with
  | [ H : ?T |- _ ] =>
    lazymatch type of T with
    | Prop =>
      let x := numgoals in
      inversion H;
      fail_if_dup;
      let y := numgoals in
      guard x >= y;
      subst; clear_tauto_eq; clear_dups
    end
  end.

Ltac progressive_inversions :=
  clear_dups;
  repeat progressive_inversion.

Ltac destruct_logic :=
  destruct_one_pair || destruct_one_ex ||
                    match goal with
                    | [ H : ?X \/ ?Y |- _ ] => destruct H
                    | [ ev : { _ } + { _ } |- _ ] => destruct ev
                    | [ ev : _ + { _ } |- _ ] => destruct ev
                    end.

Ltac destruct_all := repeat destruct_logic.

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

Ltac pick_fresh_do tac :=
  let L := gather_atoms in
  let L := beautify_fset L in
  tac L.

Ltac doit from num tac :=
  match from with
  | num =>  idtac
  | _ => tac from; doit (S from) num tac
  end.

Ltac cofinite :=
  match goal with
  | [  |- forall _, _ `notin` ?L' -> _ ] =>
    is_evar L';
    let x := fresh "x" in
    pick_fresh_do ltac:(fun L => unify L' L);
    let Fr := fresh "Fr" in
    intros x Fr
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


Ltac find_intro tac term :=
  match goal with
  | [ |- forall _ : ?T, _ ] =>
    let H := fresh "H" in
    intro H;
    match type of H with
    | context[term] =>
      tac H
    | _ => 
      find_intro tac term
    end
  | [ |- _ ] =>
    fail 1 "cannot find an induction target of " term
  end.

Tactic Notation "induction" "on" constr(term) :=
  find_intro ltac:(fun H => induction H) term.

Tactic Notation "dep" "induction" "on" constr(term) :=
  find_intro ltac:(fun H => dependent induction H) term.

(** https://sympa.inria.fr/sympa/arc/coq-club/2018-03/msg00087.html *)
Ltac fold_not_under_forall :=
   repeat
     match goal with
     | H : forall n : ?T, @?x n |- _ =>
       match type of H with
       | context[False] => idtac
       end;
       match x with
       | fun n : T => ?b =>
         let not_n := fresh in
         let b''' :=
             constr:(
               fun n : T =>
                 match b with
                 | not_n =>
                   ltac:(let b' := (eval cbv delta [not_n] in not_n) in
                         match b' with
                         | context C[?P -> False] =>
                           let b'' := context C[~ P] in
                           exact b''
                         end)
                 end) in
         let tH' := eval cbn beta in (forall n : T, b''' n) in
         let tH := type of H in
         change tH with tH' in H
       end
     end.

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

Tactic Notation "exrewrite" uconstr(lem) :=
  exexec lem ltac:(fun l => rewrite l).

Tactic Notation "eexrewrite" uconstr(lem) :=
  exexec lem ltac:(fun l => erewrite l).

Tactic Notation "contextual" "apply" uconstr(lem) :=
  match goal with
  | [H : ?P |- _ ] =>
    match type of P with Prop => apply lem in H end
  end.

Tactic Notation "contextual" "eapply" uconstr(lem) :=
  match goal with
  | [H : ?P |- _ ] =>
    match type of P with Prop => eapply lem in H end
  end.


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

Ltac reassoc_impl lst assoc :=
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

Ltac app_lists lists :=
  let rec appl l :=
      match type of l with
      | list (list ?T) => match l with
                         | ?h :: nil => h
                         | ?h :: ?t => let y := appl t in constr:(h ++ y)
                         | nil => constr:(@nil T)
                         end
      end in
  let rec col l :=
      match type of l with
      | list (list (list ?T)) =>
        match l with
        | ?h :: ?t => let x := appl h in
                     let y := col t in constr:(x :: y)
        | nil => constr:(@nil (list T))
        end
      end in
  let x := col lists in appl x.

Ltac collect_list apps n :=
  let rec col ap m := match constr:((ap, m)) with
                      | (?l1 ++ ?l2, S ?o) =>
                        let r := col l2 o in constr:(l1 :: r)
                      | (_ ++ _, 0) => fail 1
                      | (_, S _) => fail 1
                      | (_, 0) => constr:(ap :: nil)
                      end in
  col apps n.

(** here comes the tactic that is going to reassociate the lists.
 * it does following things:
 * 1. simplify environment into canonical form;
 * 2. find out a list that is the result of appending precisely N lists together;
 * 3. reassociate them according to ASSOC;
 * 4. prove the new one and the old one are the same by calling TAC.
 *)
Ltac doreassoc n assoc tac :=
  let rec all_at_most l :=
      match l with
      | ?h :: ?t => match n with context[h] => all_at_most t end
      | nil => idtac
      | _ => fail "the list has element greater than" n
      end in
  all_at_most assoc; non_dec_list assoc; (* input sanity checking *)
  lazymatch n with
  | S ?n' => 
    simpl_env;
    match goal with
    | [  |- context[?l ++ ?ls] ] =>
      let colists := collect_list (l ++ ls) n' in
      let reac := reassoc_impl colists assoc in
      let applist := app_lists reac in
      let expr := constr:(l ++ ls) in
      replace expr with applist by tac
      || fail "unable to prove association holds:" expr "=" applist
    end
  end.


Tactic Notation "reassoc" constr(n) "with" constr(c1) "by" "[" tactic(tac) "]" :=
  doreassoc n (c1 :: nil) ltac:(tac).

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2)
       "by" "[" tactic(tac) "]" :=
  doreassoc n (c1 :: c2 :: nil) ltac:(tac).

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2) constr(c3)
       "by" "[" tactic(tac) "]" :=
  doreassoc n (c1 :: c2 :: c3 :: nil) ltac:(tac).

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2) constr(c3) constr(c4)
       "by" "[" tactic(tac) "]" :=
  doreassoc n (c1 :: c2 :: c3 :: c4 :: nil) ltac:(tac).

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2) constr(c3) constr(c4) constr(c5)
       "by" "[" tactic(tac) "]" :=
  doreassoc n (c1 :: c2 :: c3 :: c4 :: c5 :: nil) ltac:(tac).

(* List Reassociation Ends Here. *)

Ltac try_discharge :=
  try congruence.

Ltac careful_unfold :=
  autounfold in *;
  fold any not; fold_not_under_forall. (* we don't want to unfold not *)

Ltac simplify :=
  simpl in *; cbn in *; subst;
  careful_unfold.

(** there occasionally will be cheap goals that can be discharged
 * by direct application.
 *)
Ltac direct_app :=
  match goal with
  | [ H: context[_ /\ ?G] |- ?G ] => apply H
  | [ H: context[?G /\ _] |- ?G ] => apply H    
  end;
  repeat destruct_eq; destruct_all.

Ltac progressive_destruction :=
  destruct_eq || destruct_logic
  || (match goal with
         | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
     end; try congruence; subst)
  || (clear_dups; progressive_inversion).

Ltac progressive_destructions :=
  repeat progressive_destruction.


(** These tactics are for further modifications such that routine tactic can
 * be extended with further concepts that are not visible in this module.
 *
 * TODO: is there a better way to do injection? *)
Ltac routine_subtac1 := idtac.

Ltac routine_subtac2 := idtac.

(** The skeleton of decision procesure.
 * unfortunately, the undecidability of this language is too complex
 * to handle by tactics that solves purely logical problems. 
 * TODO: see where autorewrite can be applied. *)
Ltac routine_impl prep tac :=
  intros; try cofinite;
  try solve_by_invert;
  prep;
  simplify;
  progressive_destructions;
  simplify;
  (* (repeat f_equal) is too aggressive. we might over do it.
   * the workaround is to trivial to solve goal heuristically and 
   * only repeat if we cannot solve the goal via cheap tactics. *)
  repeat (f_equal; try eassumption; try congruence);
  try direct_app;
  repeat (split; autounfold; simpl; cbn; intros);
  routine_subtac1;
  routine_subtac2;
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

Tactic Notation "routine" "at" int(n) :=
    routine_impl ltac:(idtac) ltac:(idtac; try assumption; try_discharge; auto n).

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


Tactic Notation "eroutine" "at" int(n) :=
  routine_impl ltac:(idtac) ltac:(idtac; try assumption; try_discharge; eauto n).

(** the point of this tactic is to switch goal to another one.
 * consider a chain of implications: A => B, B => C,
 * it's clear that implication is transitive relation.
 * therefore, from A to C might be difficult, 
 * while if B is given, the two parts might be able to discharged by 
 * automated tactics.
 *)
Ltac prove_instead trm tac :=
  intros; simplify;
  assert trm;
  match goal with
  | [ H : trm |- ?G ] =>
    tac
  | _ => idtac (* we don't deal with trm *)
  end.

Tactic Notation "prove" constr(trm) "instead" "by[" tactic(tac) "]" :=
  prove_instead trm tac.

Tactic Notation "prove" constr(trm) "instead" :=
  prove trm instead by[ routine ].

Tactic Notation "eprove" constr(trm) "instead" :=
  prove trm instead by[ eroutine ].

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

Tactic Notation "reassoc" constr(n) "with" constr(c1) :=
  reassoc n with c1 by [routine].

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2) :=
    reassoc n with c1 c2 by [routine].

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2) constr(c3) :=
    reassoc n with c1 c2 c3 by [routine].

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2) constr(c3) constr(c4) :=
    reassoc n with c1 c2 c3 c4 by [routine].

Tactic Notation "reassoc" constr(n)
       "with" constr(c1) constr(c2) constr(c3) constr(c4) constr(c5) :=
    reassoc n with c1 c2 c3 c4 c5 by [routine].

(** PRIMITIVES *)

Definition not_empty {A : Type} (l : list A) : Prop :=
  match l with
  | nil => False
  | cons _ _ => True
  end.
(* Hint Unfold not_empty. *)

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

Module LabelSetImpl <: FSetExtra.WSfun Label := FSetExtra.Make Label.

Module LabelSetNotin := FSetWeakNotin.Notin_fun Label LabelSetImpl.

Module LabelAssocList := AssocList.Make Label LabelSetImpl.

Notation lbinds := LabelAssocList.binds.
Notation luniq := LabelAssocList.uniq.
Notation lmap := LabelAssocList.map.
Notation ldom := LabelAssocList.dom.
Notation ladd := LabelSetImpl.add.

Notation lIn := LabelSetImpl.In.
Notation "x `lnotin` E" := (~ lIn x E) (at level 70).

Hint Constructors luniq.

(* taken code from metalib to make life easier. *)

Notation luniq_one := LabelAssocList.uniq_one_1.
Notation luniq_cons := LabelAssocList.uniq_cons_3.
Notation luniq_app := LabelAssocList.uniq_app_4.
Notation luniq_map := LabelAssocList.uniq_map_2.

Notation lbinds_one := LabelAssocList.binds_one_3.
Notation lbinds_cons := LabelAssocList.binds_cons_3.
Notation lbinds_app_l := LabelAssocList.binds_app_2.
Notation lbinds_app_r := LabelAssocList.binds_app_3.
Notation lbinds_map := LabelAssocList.binds_map_2.

Notation lnotin_empty := LabelSetNotin.notin_empty_1.
Notation lnotin_add := LabelSetNotin.notin_add_3.
Notation lnotin_singleton := LabelSetNotin.notin_singleton_2.
Notation lnotin_union := LabelSetNotin.notin_union_3.

Ltac solve_label_notin :=
  try eassumption;
  autorewrite with rewr_dom in *;
  LabelSetNotin.destruct_notin;
  repeat first [ apply lnotin_union
               | apply lnotin_add
               | apply lnotin_singleton
               | apply lnotin_empty
               ];
  try tauto.

Hint Extern 1 (_ `lnotin` _) =>
match goal with
| [ |- ?l `lnotin` _ ] => solve_label_notin
end.

Hint Resolve
  LabelSetImpl.add_1 LabelSetImpl.add_2 LabelSetImpl.remove_1
  LabelSetImpl.remove_2 LabelSetImpl.singleton_2 LabelSetImpl.union_2
  LabelSetImpl.union_3 LabelSetImpl.inter_3 LabelSetImpl.diff_3.

(* try to deal with uniq for labels. *)
Hint Resolve luniq_one luniq_cons luniq_app luniq_map.

Ltac ldestruct_uniq := LabelAssocList.destruct_uniq.
Ltac lsolve_uniq := LabelAssocList.solve_uniq.

(* TODO: this is purely wrong to have a timeout here.
 * however, solve_uniq calls fsetdec which might not come back in
 * near future. try to write another uniq solver.
 *)
Ltac luniq_routine :=
  try ldestruct_uniq;
  try match goal with [ |- luniq _ ] => let s := TIMEOUT in timeout s lsolve_uniq end.

Ltac routine_subtac1 ::= luniq_routine.

(* OTHER HINTS *)

(* always try to invert on non-empty universal quantification on lists *)
Hint Extern 1 => match goal with
                | [ H: Forall _ (_ :: _) |- _ ] => inversion H; clear H
                end.

(* try to deal with uniq for atoms *)
Hint Resolve uniq_one uniq_cons uniq_app uniq_map uniq_cons_1.

(* some easy stuff *)

Section LAListProps.
  Variable B : Type.
  Variable T : Type.

  Context {LIso : ListIso (label * B) T}.

  Lemma binds_witness : forall a (b : B) l1 l2,
      lbinds a b (to_list $ append l1 $ from_list $ (a, b) :: l2).
  Proof.
    intros. rewrite append_sound.
    remember (to_list l1) as L. generalize L.
    induction on list; simpl.
    - rewrite to_from_iso. auto.
    - right. trivial.
  Qed.

End LAListProps.

(* strange that this general law is not provided from the library *)
Lemma Forall_concat : forall A (l l' : list A) P,
    Forall P l ->
    Forall P l' ->
    Forall P (l ++ l').
Proof. induction on Forall; routine. Qed.
Hint Resolve Forall_concat.
