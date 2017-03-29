Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Narrowing.
Require Import Has_member.
Require Import Tight_bound_completeness.
Require Import Tight_possible_types.
Require Import Good_types.
Require Import General_to_tight.
(*Require Import Misc_inversions.*)

Lemma ctx_binds_to_sto_binds_typing: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_sto_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; auto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm; auto.
  rewrite concat_assoc.
  eapply wf_sto_to_ok_G; eauto.
Qed.

Lemma wf_sto_val_new_in_G': forall G s x T,
  wf_sto G s ->
  binds x (typ_bnd T) G ->
  exists ds, binds x (val_new T ds) s.
Proof.
  introv Hwf Bis.
  assert (exists v, binds x v s) as Bi. {
    eapply ctx_binds_to_sto_binds; eauto.
  }
  destruct Bi as [v Bi].
  lets Hc: (ctx_binds_to_sto_binds_typing Hwf Bis). destruct Hc as [v' [Hv HT]].
  destruct (corresponding_types Hwf Bis).
  - destruct H as [? [? [? [Bis' _]]]].
    pose proof (binds_func Hv Bis') as Hv'. subst. inversion HT. subst.
    assert (ty_precise = ty_precise) as Hobv by reflexivity. destruct (H Hobv) as [x3 Contra]. inversion Contra.
  - destruct H as [S [ds' [Hb [Hn He]]]]. inversions He. exists ds'.
    assumption.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G s x T U,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  pose proof (wf_good Hwf) as Hgd.
  pose proof (general_to_tight_typing Hwf Hty) as Hti.
  pose proof (tight_to_precise_typ_all Hwf Hti) as [S' [T' [Hpt [Hsub [HSsub [L' HTsub]]]]]].
  pose proof (good_precise_all_inv Hgd Hpt) as Bi.
  pose proof (corresponding_types Hwf Bi) as [[T2 [U2 [t [Hb [Hl HS]]]]] | [? [? [? [? HS]]]]];
  inversion HS.
  subst T2 U2; clear HS.
  inversion Hl; subst.
  - exists (dom G \u L \u L') S' t.
    split; auto.
    pose proof (tight_possible_types_lemma Hgd Hti) as Htp.
    inversion Htp; subst.
    + apply (good_precise_all_inv Hgd) in Hpt.
      apply (good_precise_all_inv Hgd) in H.
      pose proof (binds_func Hpt H) as H4.
      inversion H4; subst T U; clear H4.
      split; auto.
    + apply tight_to_general in HSsub; auto.
      split; auto.
      subst.
      intros y Hfr.
      eapply ty_sub.
      intros Contra; inversion Contra.
      eapply narrow_typing.
      eapply H3; eauto.
      apply subenv_last; auto.
      apply ok_push. eapply wf_sto_to_ok_G; eauto. auto.
      apply ok_push. eapply wf_sto_to_ok_G; eauto. auto.
      auto.
  - pose proof (H (eq_refl _)) as [? Contra]; inversion Contra.
Qed.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T.

*)
Lemma canonical_forms_2: forall G s x a T,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_rcd (dec_trm a T)) ->
  (exists S ds t, binds x (val_new S ds) s /\ ty_defs G (open_defs x ds) (open_typ x S) /\ defs_has (open_defs x ds) (def_trm a t) /\ ty_trm ty_general sub_general G t T).
Proof.
  (*
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [S' [ds [t' [Heq [Hdefs Htyd]]]]].
  subst.
  exists S' ds t'.
  split; try split; try split; try assumption.
  eapply new_ty_defs; eauto.
Qed.
*)
Admitted.
