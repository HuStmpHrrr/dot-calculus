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
| ty_obj_typ_inv : forall G x A (DS1 DS2 : decs) S1 T1 S2 T2,
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


Lemma invertible_typing_closure_tight: forall G x T U,
    inert_env G ->
    G ⊢## x ⦂ T ->
    G ⊢# T <⦂ U ->
    G ⊢## x ⦂ U.
Proof.
  induction on subtypt; eroutine.
  (* all:inv typing undec 1; *)
  (*   eprove from inert at 6. *)
  prove from inert.
  Focus 3.
  prove from inert.
  Focus 3.
  eprove from inert at 6.
  Focus 3.
  invert H4; prove from inert.

  eapply ty_obj_fld_inv. eassumption.
  
  eprove from inert at 6.
  prove from inert.
  eprove from inert at 6.
  eprove from inert.
  all: inv typing undec 1.
  prove from inert.
  induction on subtypt; eroutine;
    inv typing undec 1;
    eprove from inert at 6.
Qed.

Lemma tight_to_invertible : forall G (x : var) U,
    inert_env G ->
    G ⊢# trm_var x ⦂ U ->
    G ⊢## x ⦂ U.
Proof.
  dep induction on tyt_trm; auto.
  eapply invertible_typing_closure_tight; try eassumption.
  eauto.
Qed.


Lemma inert_subtyp_obj : forall G x DS L D,
    inert_env G ->
    G ⊢## x ⦂ μ{ DS } ->
    lbinds L D DS ->
    exists DS' D', binds x (μ{ DS' }) G /\ lbinds L D' DS'.
Proof.
  dep induction on ty_var_inv; intros;
    eauto.
  do 2 eexists. eroutine.
  routine.
Qed.

(* Lemma inert_natural_obj_subtyp : forall G x DS A S U, *)
(*     inert_env G -> *)
(*     G ⊢## x ⦂ μ{ DS } -> *)
(*     lbinds (label_typ A) (dec_typ S U) DS -> *)
(*     forall DS' T, *)
(*       binds x (μ{ DS' }) G -> *)
(*       lbinds (label_typ A) (dec_typ T T) DS' -> *)
(*       G ⊢# S <⦂ T /\ G ⊢# T <⦂ U. *)
(* Proof. *)
(*   intros G x DS A S U. intro. intro. gen S U H0. *)
(*   dep induction on ty_var_inv; *)
(*     intros. *)
(*   Focus 6. *)
(*   from_inert. *)
(*   destruct (A == A0). subst. *)
(*   split. apply subtypt_trans with S1. eapply H2. *)
  
(*   list_reasoning. *)
(*   eapply IHty_var_inv; eauto. list_reasoning. *)
(*   repeat (apply LabelAssocList.binds_app_1 in H3; destruct H3); auto. *)
(*   routine. *)

  
(*   eapply IHty_var_inv; eauto. list_reasoning. *)
(*   repeat (apply LabelAssocList.binds_app_1 in H3; destruct H3); auto. *)
(*   routine. *)
  
  
(*   from_inert; auto. *)
(*   from_inert; list_reasoning. eapply IHty_var_inv; eauto; list_reasoning; apply lbinds_app_r; auto. *)
(*   from_inert; list_reasoning. eapply IHty_var_inv; eauto; list_reasoning; apply lbinds_app_l; auto. *)



Lemma general_to_tight :
  forall G0, inert_env G0 ->
        (forall G t T, G ⊢ t ⦂ T ->
                  G = G0 ->
                  G ⊢# t ⦂ T) /\
        (forall G S U, G ⊢ S <⦂ U ->
                  G = G0 ->
                  G ⊢# S <⦂ U).
Proof.
  mutual induction; eroutine.

  recover_inert_env.
  (* we need to prove inert_env gives a good binding *)
  specialize (H0 eq_refl).

  invert H0; eauto.
  subst.
  apply tight_to_invertible in H3; auto.
  pose proof H4.
  eapply invertible_typing_closure_tight in H5.
  instantiate (1 := x) in H5. all:trivial.
  apply inert_subtyp_obj in H5.
  destruct H5.
  from_inert.
  
  pose proof invertible_typing_closure_tight.
  specialize (H5 term+)
  
  eauto.
  
  eapply subtypt_sel1.
  
  
  tight typing undec 1; routine.
  apply H1.
  
  eapply subtypt_all; auto.

  
  tight typing undec 1; eroutine.


(* Hint Extern 1 => *)
(* list_reasoning; apply lbinds_app_r. *)

(* Hint Extern 1 => *)
(* list_reasoning; apply lbinds_app_l. *)


(* Hint Resolve lbinds_app_r. *)

(* Require Import Metalib.CoqEqDec. *)

(* Instance EqDec_typ_label typ_label : EqDec_eq typ_label. *)
(* Proof. *)
(* Admitted. *)

(* Lemma inert_natural_obj_subtyp : forall G x DS A S U, *)
(*     inert_env G -> *)
(*     G ⊢## x ⦂ μ{ DS } -> *)
(*     lbinds (label_typ A) (dec_typ S U) DS -> *)
(*     forall DS' T, *)
(*       binds x (μ{ DS' }) G -> *)
(*       lbinds (label_typ A) (dec_typ T T) DS' -> *)
(*       G ⊢# S <⦂ T /\ G ⊢# T <⦂ U. *)
(* Proof. *)
(*   intros G x DS A S U. intro. intro. gen S U H0. *)
(*   dep induction on ty_var_inv; *)
(*     intros. *)
(*   Focus 6. *)
  (* from_inert. *)
  (* destruct (A == A0). subst. *)
  (* split. apply subtypt_trans with S1. eapply H2. *)
  
  (* list_reasoning.  *)
  (* eapply IHty_var_inv; eauto. list_reasoning. *)
  (* repeat (apply LabelAssocList.binds_app_1 in H3; destruct H3); auto. *)
  (* routine. *)

  
  (* eapply IHty_var_inv; eauto. list_reasoning. *)
  (* repeat (apply LabelAssocList.binds_app_1 in H3; destruct H3); auto. *)
  (* routine. *)
  
  
  (* from_inert; auto. *)
  (* from_inert; list_reasoning. eapply IHty_var_inv; eauto; list_reasoning; apply lbinds_app_r; auto. *)
  (* from_inert; list_reasoning. eapply IHty_var_inv; eauto; list_reasoning; apply lbinds_app_l; auto. *)

  (* from_inert. list_reasoning. *)
  (* apply LabelAssocList.binds_app_1 in H1. *)
  (* progressive_destructions. *)
  (* eauto. eauto. *)

  (* from_inert. eapply IHty_var_inv; eauto; list_reasoning. *)
  (* apply LabelAssocList.binds_app_1 in H0. *)
  (* destruct H0. eauto. *)
  (* apply LabelAssocList.binds_app_1 in H0. *)
  (* destruct H0. cbv in H0. routine. eauto. *)

  (* from_inert. eapply IHty_var_inv. eauto. list_reasoning. *)
  (* repeat (apply LabelAssocList.binds_app_1 in H3; destruct H3); auto. *)
  (* routine. *)


  
  (* cbv in H1. destruct H1. inversion H1. subst. *)
  (* routine. *)
  (* routine. *)
  
  (* eauto. *)
  (* change (decs_cons a (dec_trm U) DS2) with (decs_append (decs_cons a (dec_trm U) decs_nil) DS2) in H0. *)
  (* list_reasoning. *)

  
  (* routine. *)
  
  (* eapply IHty_var_inv; auto. *)
  

  
  (* from_inert_env; *)
  (* clear_dups; from_inert_obj. *)


  
  (* prove from inert. *)

  
(*   progressive_destructions. *)
(*   clear_dups. recover_inert_env. *)

(*   simpl in *; cbn in *; subst. *)
(*   autounfold in *; fold any not. *)
  

  
(*   simplify. *)
(*   prove from inert. *)
  
(*   from_inert. *)
(*   prove from inert. *)

(*     prove from inert. *)
(*     intros. *)
(*   from_inert_env. clear_dups. *)
(*   match goal with *)
(*   | [ H : inert_env ?G, H1 : binds ?x ?T1 ?G, H2 : binds ?x ?T2 ?G |- _ ] => *)
(*     different T1 T2; *)
(*       assert (T1 = T2); subst *)
(*   end. *)
(*   simplify; progressive_destructions. *)
(*   fail_if_dup. dup_eq. *)
(*   eapply binds_unique; eauto. *)
  
(*    by (fail_if_dup; dup_eq; *)
(*                            eapply binds_unique; eassumption) *)
  
(*   from_inert. from_inert_env.  from_inert. clear_dups. *)
(*   prove from inert. *)
   
(*     prove from inert. *)

  
(*   intros. *)


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
(*     + subst. right. *)
(*     subst. *)
(*   auto. *)
(*   induction on tyt_trm. *)
