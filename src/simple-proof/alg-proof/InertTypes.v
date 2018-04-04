Require Import Definitions Substitution.
Require Import Coq.Lists.List.

Inductive inert_dec : label * dec -> Prop :=
| rd_typ : forall A T, inert_dec (label_typ A ∈ T ⋯ T)
| rd_trm : forall a T, inert_dec (label_trm a ∷ T).
Hint Constructors inert_dec.


Definition inert_decs (DS : decs) :=
  not_empty DS /\ luniq DS /\ Forall inert_dec DS.
Hint Unfold inert_decs.


Lemma ty_defs_same_atoms : forall G ds DS,
    G ⊩[ ds ⦂ DS ] ->
    ldom ds = ldom DS.
Proof. induction on ty_defs; routine. Qed.


Lemma ty_defs_not_empty : forall G ds DS,
    G ⊩[ ds ⦂ DS ] ->
    not_empty ds.
Proof. routine by invert on ty_defs. Qed.
Hint Resolve ty_defs_not_empty.


Section InertObj.
  
  Local Hint Extern 1 =>
  match goal with
  | [ H : _ ⊩ (_ , _) ⦂ _ |- _ ] =>
    invert H
  | [ H : _ ⊩[ _ ⦂ _ ] |- _ ] =>
    invert H
  end.
  
  Lemma ty_defs_inert : forall G ds DS,
      wf_defs ds ->
      G ⊩[ ds ⦂ DS ] ->
      inert_decs DS.
  Proof. 
    induction on ty_defs; routine; invert on Forall; 
      constructor; eroutine.
    (* TODO: this part is very typically due to lack of
     * power for current automation to deal with rewrites.
     * anything I can do to improve this? *)
    erewrite <- ty_defs_same_atoms; eassumption.
  Qed.


  (* seem very easy on this part. *)
  Lemma open_preserves_ldom : forall k z (DS : decs),
      ldom (open_rec k z DS) = ldom DS.
  Proof. induction on decs; routine. Qed.

  
  Lemma open_dec_invert_inert : forall k z l D,
      z `notin` fv D ->
      inert_dec (l, open_rec k z D) ->
      inert_dec (l, D).
  Proof.
    destr on dec; routine by invert on inert_dec.
    context apply open_fresh_inj_typ_dec_decs; routine.
  Qed.
  Local Hint Resolve open_dec_invert_inert.
  

  Lemma open_decs_invert_inert : forall k z DS,
      z `notin` fv DS ->
      inert_decs (open_rec k z DS) ->
      inert_decs DS.
  Proof.
    induction on decs; routine;
      invert on Forall;
      constructor;
      destr on decs;
      eroutine.
    (* again! rewrites! *)
    erewrite <- open_preserves_ldom; eassumption.
  Qed.


End InertObj.

