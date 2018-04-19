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

| ty_obj_fld_inv : forall G x a T (DS1 DS2 : decs) U,
    G ⊢## x ⦂ μ{ append DS1 $ decs_cons (label_trm a) (dec_trm T) DS2 } ->
    G ⊢# T <⦂ U ->
    G ⊢## x ⦂ μ{ append DS1 $ decs_cons (label_trm a) (dec_trm U) DS2 }
| ty_obj_typ_inv : forall G (x : atom) A (DS1 DS2 : decs) S1 T1 S2 T2,
    G ⊢## x ⦂ μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 } ->
    G ⊢# S2 <⦂ S1 ->
    G ⊢# T1 <⦂ T2 ->
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
       x ~ S2 ++ G ⊢ open x T1 <⦂ open x T2) ->
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


Tactic Notation "inv" "typing" "undec" "1" :=
  match goal with
  | [H : _ ⊢## _ ⦂ _ ⋅ _ |- _ ] => invert H
  | _ => idtac
  end.


Section InvertibleTyping.
  Lemma invertible_typing_closure_tight: forall G x T U,
    inert_env G ->
    G ⊢## x ⦂ T ->
    G ⊢# T <⦂ U ->
    G ⊢## x ⦂ U.
  Proof.
    induction on subtypt; eroutine;
      inv typing undec 1;
      eprove from inert at 6.
  Qed.
  Hint Resolve invertible_typing_closure_tight.

  Lemma tight_to_invertible : forall G (x : var) U,
      inert_env G ->
      G ⊢# trm_var x ⦂ U ->
      G ⊢## x ⦂ U.
  Proof. dep induction on tyt_trm; eauto. Qed.

  Ltac boom :=
    destruct_lbinds;
    try match goal with
        | [H : _ |- _ ] =>
          guess_is_ind_hyp H;
          eapply H; eauto;
          solve_lbinds
        end.

  Lemma inert_intuitive_subtyping : forall G x DS A,
      inert_env G ->
      G ⊢## x ⦂ μ{ DS } ->
      forall S U,
      lbinds (label_typ A) (dec_typ S U) DS ->
      G ⊢# S <⦂ x ⋅ A /\ G ⊢# x ⋅ A <⦂ U.
  Proof.
    dep induction on ty_var_inv; intros;
      match goal with
      | [ _ : binds _ (μ{ ?DS }) ?G
        , _ : inert_env ?G
        , _ : lbinds _ _ (_ ?DS) |- _] =>
        (* this captures the base case *)
        eprove from inert
      | _ => boom
      end;
      match goal with
      | [H : lbinds _ _ (to_list (decs_cons _ _ decs_nil)) |- _] =>
        cbn in H; progressive_destructions
      end;
    split; econstructor; try eassumption; boom.
  Qed.

End InvertibleTyping.

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
