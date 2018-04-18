Set Implicit Arguments.

Require Import Definitions Substitution.
Require Import Coq.Lists.List.

Inductive inert_dec : label * dec -> Prop :=
| rd_typ : forall A T, inert_dec (label_typ A ∈ T ⋯ T)
| rd_trm : forall a T, inert_dec (label_trm a ∷ T).
Hint Constructors inert_dec.


Definition inert_decs (DS : decs) :=
  not_empty DS /\ luniq DS /\ Forall inert_dec DS.
Hint Unfold inert_decs.
(* Hint Transparent inert_decs. *)


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
    induction on ty_defs; routine;
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
    contextual apply open_fresh_inj_typ_dec_decs; routine.
  Qed.
  Local Hint Resolve open_dec_invert_inert.
  

  Lemma open_decs_invert_inert : forall k z DS,
      z `notin` fv DS ->
      inert_decs (open_rec k z DS) ->
      inert_decs DS.
  Proof.
    induction on decs; routine;
      constructor;
      destr on decs;
      eroutine.
    (* again! rewrites! *)
    erewrite <- open_preserves_ldom; eassumption.
  Qed.

End InertObj.

Inductive inert_typ : typ -> Prop :=
| inert_all : forall S T, inert_typ (all(S) T)
| inert_obj : forall DS, inert_decs DS -> inert_typ (μ{DS}).
Hint Constructors inert_typ.


Definition inert_env (G : env) : Prop :=
  Forall (fun tup : (atom * typ) => let (_, t) := tup in inert_typ t) G /\ uniq G.
Hint Unfold inert_env.
(* Hint Transparent inert_env. *)


(* This form of inert definitions automatically turn lots
 * of problems to triviality.
 *
 * for example:
 *)
Section TrivialLemmas.

  Hint Extern 1 =>
  match goal with
  | [ H: inert_typ _ |- _ ] => invert H
  end.
  
  Lemma binds_inert : forall G x T, inert_env G -> binds x T G -> inert_typ T.
  Proof. induction G; eroutine. Qed.
  Hint Resolve binds_inert.

  Lemma inert_env_inert_decs : forall G x DS,
      inert_env G ->
      binds x (μ{ DS }) G ->
      inert_decs DS.
  Proof.
    intros.
    prove (inert_typ $ μ{ DS }) instead by[ auto ].
    eroutine.
  Qed.
  
  Lemma inert_concat : forall G G',
      inert_env G -> inert_env G' ->
      uniq (G' ++ G) ->
      inert_env (G' ++ G).
  Proof. routine. Qed.

  Local Hint Extern 1 =>
  match goal with
  | [ H: inert_dec _ |- _ ] =>  invert H
  end.

  Lemma invert_inert_decs : forall DS l D,
      inert_decs DS ->
      lbinds l D DS ->
      inert_dec (l, D).
  Proof. induction DS; [| destruct DS]; routine. Qed.
  Hint Resolve invert_inert_decs.
  Arguments invert_inert_decs {DS l D}.

  
  Lemma inert_decs_also_dec : forall DS A S T,
      inert_decs DS ->
      lbinds (label_typ A) (dec_typ S T) DS ->
      S = T.
  Proof. routine by contextual apply invert_inert_decs. Qed.
  Local Hint Resolve inert_decs_also_dec.

  
  Lemma binds_inert_obj : forall G x DS A S T,
      inert_env G ->
      binds x (μ{ DS }) G ->
      lbinds (label_typ A) (dec_typ S T) DS ->
      S = T.
  Proof. induction G; eroutine. Qed.

  Lemma binds_inert_obj_lbinds : forall G x DS A S T,
      inert_env G ->
      binds x (μ{ DS }) G ->
      lbinds (label_typ A) (dec_typ S T) DS ->
      lbinds A (dec_typ S S) DS /\ lbinds A (dec_typ T T) DS.
  Proof.
    routine by idtac; match goal with
                      | [ H : binds _ _ _ |- _ ] =>
                        eapply binds_inert_obj in H
                      end.
  Qed.
  
End TrivialLemmas.
Hint Resolve inert_concat invert_inert_decs inert_concat.


(* Inert Related Tactics Goes Following *)

Ltac recover_inert_env :=
  repeat match goal with
         | [ G : env |- _ ] =>
           assert (inert_env G) by auto; fail_if_dup
         end.

Ltac inert_env_conseqs :=
  repeat
    match goal with
    (* case 1: DS must be inert. *)
    | [ H : inert_env ?G, H1 : binds _ (μ{ ?DS }) ?G |- _ ] =>
      pose H1 apply inert_env_inert_decs; auto; fail_if_dup
    (* case 2: inert env is a uniq env *)
    | [ H : inert_env ?G, H1 : binds ?x ?T1 ?G, H2 : binds ?x ?T2 ?G |- _ ] =>
      different T1 T2;
      assert (T1 = T2) by (fail_if_dup; dup_eq;
                           eapply binds_unique; eassumption); subst
    (* case 3: something must be inert type. *)
    | [ H : inert_env ?G, H1 : binds _ _ ?G |- _ ] =>
      pose H1 apply binds_inert; auto; fail_if_dup
    end.

(** this tactic derives consequences from inert environment. *)
Ltac from_inert_env :=
  progressive_destructions;
  (* let's recover inert_env first. *)
  clear_dups; recover_inert_env;
  inert_env_conseqs.

Ltac from_inert_obj :=
  repeat
    (progressive_destruction
     || match goal with
       | [ H : inert_decs ?DS,
           H1 : lbinds ?x ?D1 (decs_to_list ?DS),
           H2 : lbinds ?x ?D2 (decs_to_list ?DS) |- _ ] =>
         different D1 D2;
         assert (D1 = D2) by (fail_if_dup; dup_eq;
                              eapply LabelAssocList.binds_unique; routine);
         subst
       | [ H : inert_decs ?DS, H1 : lbinds ?x ?D1 (decs_to_list ?DS) |- _] =>
         pose H1 eapply binds_inert_obj_lbinds;
         try eassumption; destruct H1; fail_if_dup
       end).

Ltac from_inert :=
  from_inert_env; clear_dups; from_inert_obj.

Tactic Notation "prove" "from" "inert" := from_inert; routine.
Tactic Notation "eprove" "from" "inert" := from_inert; eroutine.
Tactic Notation "eprove" "from" "inert" "at" "6" := from_inert; eroutine at 6.
