Require Import Metalib.Metatheory.

Notation "f $ x" := (f x) (at level 68, right associativity, only parsing).

Notation "<[ e1 ; .. ; en ]>" := (cons e1 .. (cons en nil) .. ) (at level 39).

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.


Ltac destruct_all :=
  match goal with
  | [ H : ?X \/ ?Y |- _ ] => destruct H
  | [ H : ?X /\ ?Y |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  | [  |- _ ] => fail 1
  end; try destruct_all.

Ltac destruct_eq :=
  destruct_notin;
  match goal with
    | [ |- context[if ?x == ?y then _ else _]] => destruct (x == y)
  end.

Ltac equality :=
  simpl in *; try congruence;
  destruct_eq;
  auto; try congruence.
