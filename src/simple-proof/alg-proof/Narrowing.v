Require Import Definitions.

Require Import SubEnv.
Require Import Weakening.

Section NarrowingPrep.

  Local Hint Extern 1 =>
  match goal with
  | [ |- _ ((?x, ?T) :: ?G) _ _ ] =>
    replace ((x, T) :: G) with (nil ++ x ~ T ++ G) by auto
  end.
  
  Local Hint Extern 1 => eexapply weaken_rules.
  
  Lemma narrow_var :
    forall G G' x T,
      G' ⪯ G ->
      binds x T G ->
      G' ⊢ trm_var x ⦂ T.
  Proof.
    induction on subenv; auto; intros;
    match goal with
    | [ H : binds _ _ _ |- _ ] =>
      apply binds_cons_1 in H; destruct_all; subst; eapply ty_sub
    end;
    eauto.
  Qed.
  
End NarrowingPrep.

Section Narrowing.

  Local Notation narrowing ctor :=
    (forall G t T, ctor G t T -> forall G',
          G' ⪯ G ->
          ctor G' t T).

  Lemma narrow_rules :
    narrowing ty_trm /\ narrowing ty_def /\ narrowing ty_defs /\
    narrowing subtyp.
  Proof.
    mutual induction; routine;
      try (eapply narrow_var; eassumption);
      typing undec 1;
      match goal with
      | [ H : _ ⪯ _ |- _ ] => pose proof (subenv_implies_uniq H)
      end;
      eroutine by (idtac; try cofinite; try unfold wf_defs in *).
      all:eauto 6.
  Qed.
End Narrowing.
