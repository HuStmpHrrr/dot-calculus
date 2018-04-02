Require Import Definitions Substitution.

Inductive inert_dec : label * dec -> Prop :=
| rd_typ : forall A T, inert_dec (label_typ A ∈ T ⋯ T)
| rd_trm : forall a T, inert_dec (label_trm a ∷ T).
Hint Constructors inert_dec.

Definition inert_decs (DS : decs) :=
  not_empty DS /\ luniq DS /\ list_pred inert_dec DS.
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
    induction on ty_defs; routine; invert on @list_pred; 
      constructor; eroutine.
    erewrite <- ty_defs_same_atoms; eassumption.
  Qed.

End InertObj.

(* seem very easy on this part. *)
Lemma open_preserves_ldom : forall k z (DS : decs),
    ldom (open_rec k z DS) = ldom DS.
Proof. induction on decs; routine. Qed.


