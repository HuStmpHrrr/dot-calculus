
Require Import Definitions.

Section Weakening.

  Local Notation weakening ctor :=
    (forall G t T, ctor G t T -> forall G1 G2 G3,
          G = G1 ++ G3 ->
          uniq (G1 ++ G2 ++ G3) ->
          ctor (G1 ++ G2 ++ G3) t T).

  (*
   * to tackle this lemma, it's a bit tricky, as we need
   * to understand what's the condition for discharging 
   * both ty rules and subtyp rules.
   *)

  (** this tactic massages the goal and then apply the
   * proper induction hypothesis in the context *)
  Local Ltac ind_massage x :=
    match goal with
    | [ |- context[_ ~ _ ++ _ ++ _ ++ _] ] =>
      simpl; pick_fresh_do x ltac:(fun L => instantiate (1 := L))
    | [ |- context[_ :: _ ++ _ ++ _]] =>
      pick_fresh_do x ltac:(fun L => instantiate (1 := L))
    | _ =>
      intros; simpl; eauto
    end;
    match goal with
    | [ H : context[_ `notin` _ -> _] |- context[?tup :: ?G1 ++ ?G2 ++ ?G3] ] =>
      match type of H with
      | context[_ ++ _ ++ _] =>
        replace (tup :: G1 ++ G2 ++ G3)
          with (([tup] ++ G1) ++ G2 ++ G3) by auto;
          eapply H; simpl_env
      end
    end.

  (** master tactic for this lemma *)
  Local Ltac boom :=
    let x := fresh "x" in ind_massage x; auto.
  
  Lemma weaken_rules:
    weakening ty_trm /\ weakening ty_def /\
    weakening ty_defs /\ weakening subtyp.
  Proof.
    mutual induction; intros; subst;
      match goal with
      | [ |- _ ⊢ _ ⦂ _ ] => econstructor; boom
      | [ |- context[typ_all] ] => eapply subtyp_all
      | [ |- context[dec_trm]] => eapply subtyp_fld
      | [ |- context[dec_typ]] => eapply subtyp_typ
      | [ |- context[ _ ⊢ _ <⦂ _ ⋅ _]] => eapply subtyp_sel1
      | [ |- context[ _ ⊢ _ ⋅ _ <⦂ _]] => eapply subtyp_sel2
      | _ => idtac
      end; boom.
  Qed.

End Weakening.