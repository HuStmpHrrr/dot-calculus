Set Implicit Arguments.

Require Import Definitions.

Reserved Notation "G1 ⪯ G2" (at level 70).

Inductive subenv: env -> env -> Prop :=
| subenv_empty : nil ⪯ nil
| subenv_grow: forall G G' x T T',
    G ⪯ G' ->
    uniq ((x, T) :: G) ->
    uniq ((x, T') :: G') ->
    G ⊢ T <⦂ T' ->
    (x, T) :: G ⪯ (x, T') :: G'
where "G1 ⪯ G2" := (subenv G1 G2).
Hint Constructors subenv.

Section SubEnvProps.

  Local Hint Resolve uniq_cons_1.
  Lemma subenv_refl : forall G, uniq G -> G ⪯ G.
  Proof. induction G; eroutine. Qed.
  Local Hint Resolve subenv_refl.

  Lemma subenv_push : forall G1 G2 x T,
      G1 ⪯ G2 ->
      uniq ((x, T) :: G1) ->
      uniq ((x, T) :: G2) ->
      (x, T) :: G1 ⪯ (x, T) :: G2.
  Proof. induction G1; eroutine. Qed.
  Local Hint Resolve subenv_push.

  Local Hint Extern 1 =>
  match goal with
  | [ H : uniq _ |- _ ] => inversion H
  end.

  Local Hint Extern 1 =>
  match goal with
  | [ H : _ ⪯ _ |- _ ] => inversion H
  end.
  
  Lemma subenv_last: forall G x S U,
      G ⊢ S <⦂ U ->
      uniq ((x, S) :: G) ->
      (x, S) :: G ⪯ (x, U) :: G.
  Proof. routine. Qed.

  Lemma subenv_implies_uniq : forall G1 G2,
      G1 ⪯ G2 -> uniq G1 /\ uniq G2.
  Proof. routine. Qed.

  Require Import Coq.Program.Equality.
    
End SubEnvProps.

Hint Resolve subenv_refl subenv_push subenv_last.