Require Import Definitions TightTyping.
Require Import InertTypes.


Reserved Notation "G '⊢##' x '⦂' T" (at level 70, T at level 79).


Inductive ty_var_inv : env -> atom -> typ -> Prop :=
| ty_v_inv : forall G x T, binds x T G -> G ⊢## x ⦂ T
| ty_obj_drop1_inv : forall G x (DS1 DS2 : decs),
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢## x ⦂ μ{ append DS1 DS2 } ->
    G ⊢## x ⦂ μ{ DS2 }
| ty_obj_drop2_inv : forall G x (DS1 DS2 : decs),
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢## x ⦂ μ{ append DS1 DS2 } ->
    G ⊢## x ⦂ μ{ DS1 }
| ty_obj_merge_inv : forall G x (DS1 DS2 : decs),
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢## x ⦂ μ{ DS1 } ->
    G ⊢## x ⦂ μ{ DS2 } ->
    G ⊢## x ⦂ μ{ append DS1 DS2 }
| ty_obj_fld_inv : forall L G x a T (DS1 DS2 : decs) U,
    G ⊢## x ⦂ μ{ append DS1 $ decs_cons (label_trm a) (dec_trm T) DS2 } ->
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x
            (μ{ append DS1 $ decs_cons (label_trm a) (dec_trm T) DS2 }) ++
            G ⊢ T <⦂ U) ->
    G ⊢## x ⦂ μ{ append DS1 $ decs_cons (label_trm a) (dec_trm U) DS2 }
| ty_obj_typ_inv : forall L G x A (DS1 DS2 : decs) S1 T1 S2 T2,
    G ⊢## x ⦂ μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 } ->
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x
            (μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }) ++
            G ⊢ S2 <⦂ S1) ->
    (forall y, y `notin` L ->
          y ~ open_typ_to_context y
            (μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }) ++
            G ⊢ T1 <⦂ T2) ->
    G ⊢## x ⦂ μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S2 T2) DS2 }
| ty_obj_sel_inv : forall G x y DS S A,
    G ⊢## x ⦂ S ->
    binds y (μ{ DS }) G ->
    lbinds (label_typ A) (dec_typ S S) DS ->
    G ⊢## x ⦂ y ⋅ A
| ty_all_inv: forall L G x S1 T1 S2 T2,
    G ⊢## x ⦂ all(S1) T1 ->
    G ⊢# S2 <⦂ S1 ->
    (forall x, x `notin` L ->
       x ~ S1 ++ G ⊢ open x T1 <⦂ open x T2) ->
    G ⊢## x ⦂ all(S2) T2
| ty_top_inv : forall G x T,
    G ⊢## x ⦂ T ->
    G ⊢## x ⦂ ⊤
where "G ⊢## x ⦂ T" := (ty_var_inv G x T).
Hint Constructors ty_var_inv.


Reserved Notation "G '⊢##v' x '⦂' T" (at level 70, T at level 79).
Inductive ty_val_inv : env -> val -> typ -> Prop :=
| ty_obj_inv_v : forall L G ds DS,
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x (μ{ DS }) ++ G ⊩[ ds ⦂ DS ]) ->
    wf_defs ds ->
    G ⊢##v ν(DS){ ds } ⦂ μ{DS}
| ty_all_inv_v : forall L G T t U,
    (forall x, x `notin` L ->
          x ~ T ++ G ⊢ open x t ⦂ open x U) ->
    G ⊢##v λ( T ){ t } ⦂ all( T ) U
| ty_obj_sel_inv_v : forall G v y DS A T,
    G ⊢##v v ⦂ T ->
    binds y (μ{ DS }) G ->
    lbinds (label_typ A) (dec_typ T T) DS ->
    G ⊢##v v ⦂ y ⋅ A 
| ty_top_inv_v : forall G v T,
    G ⊢##v v ⦂ T ->
    G ⊢##v v ⦂ ⊤
where "G ⊢##v v ⦂ T" := (ty_val_inv G v T).
    

(* TODO: obviously we need a tactic to record this pattern. *)
Lemma invertible_typing_closure_tight: forall G x T U,
    inert_env G ->
    G ⊢## x ⦂ T ->
    G ⊢# T <⦂ U ->
    G ⊢## x ⦂ U.
Proof.
  dep induction on subtypt; eroutine.
  - inversion H4.
    apply binds_inert in H2; routine.
  - apply ty_obj_merge_inv; routine.
  - eapply ty_obj_sel_inv; routine.
    eapply binds_inert_obj_lbinds in H1; routine.
  - invert H4; routine.
    apply binds_inert in H5; routine.
    assert (μ{DS} = μ{DS0}).
    eapply binds_unique; try eassumption.
    invert H5. subst.
    assert (inert_typ (μ{DS0})).
    eapply binds_inert; routine.
    invert H6.
    eapply binds_inert_obj_lbinds in H1; routine.
    assert (dec_typ S0 S0 = dec_typ T T).
    eapply LabelAssocList.binds_unique; try eassumption.
    invert H14. routine.
Qed.


(* Require Import Coq.Program.Equality. *)

(* Lemma inert_natural_obj_subtyp : *)
(*   forall G x DS T, inert_env G -> *)
(*               binds x (μ{ DS }) G -> *)
(*               G ⊢# trm_var x ⦂ T -> *)
(*               (exists DS', T = μ{ DS' }) \/ T = ⊤. *)
(* Proof. *)
(*   intros. gen DS H. *)
(*   dependent induction H1; intros. *)
(*   - left. exists DS. eapply binds_unique; routine. *)
(*   - edestruct IHtyt_trm; try eassumption; trivial. *)
(*     + admit. *)
(*     + subst. right.  *)
(*     subst. *)
(*   auto. *)
(*   induction on tyt_trm. *)

(* Lemma general_to_tight : *)
(*   forall G0, inert_env G0 -> *)
(*         (forall G t T, G ⊢ t ⦂ T -> *)
(*                   G = G0 -> *)
(*                   G ⊢# t ⦂ T) /\ *)
(*         (forall G S U, G ⊢ S <⦂ U -> *)
(*                   G = G0 -> *)
(*                   G ⊢# S <⦂ U). *)
(* Proof. *)
(*   mutual induction; eroutine. *)

(*   (* we need to prove inert_env gives a good binding *) *)
(*   specialize (H0 eq_refl). *)

(*   invert H0; eauto. *)
(*   subst. *)

  
(*   eauto.  *)
  
(*   eapply subtypt_sel1. *)
  
  
(*   tight typing undec 1; routine. *)
(*   apply H1. *)
  
(*   eapply subtypt_all; auto. *)

  
(*   tight typing undec 1; eroutine. *)
