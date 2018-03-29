
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
  Local Ltac ind_massage :=
    simpl; match goal with
    | [ |- context[_ :: _ ++ _ ++ _]] =>
      cofinite
    | _ =>
      intros; eauto
    end;
    match goal with
    | [ H : context[_ `notin` _ -> _] |- _ ] =>
      reassoc 4 with 2 by [ auto ];
      match type of H with
      | context[_ ++ _ ++ _] =>
          eapply H; simpl_env
      end
    end.

  (** master tactic for this lemma *)
  Local Ltac boom := ind_massage; auto.
  
  Lemma weaken_rules:
    weakening ty_trm /\ weakening ty_def /\
    weakening ty_defs /\ weakening subtyp.
  Proof.
    mutual induction*; subst; typing undec 1; boom.
  Qed.

End Weakening.