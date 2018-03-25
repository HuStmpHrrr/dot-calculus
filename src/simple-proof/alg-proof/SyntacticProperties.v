
Set Implicit Arguments.

Require Import Definitions.
Require Import LibUtils.
Require Import Coq.Lists.List.

Section ObjectProps.

  Lemma obj_exchg_equiv : forall G (DS1 DS2 : decs),
      not_empty DS1 ->
      not_empty DS2 ->
      G ⊢ μ{ append DS1 DS2 } ≊ μ{ append DS2 DS1 }.
  Proof. 
    intros; split; intros;
      constructor; auto with alg_def;
      autounfold;
      rewrite append_sound;
      match goal with
      | [  |- context[?DS1 ++ ?DS2] ] =>
        replace (DS1 ++ DS2) with (nil ++ DS1 ++ DS2) by trivial
      end;
      eapply not_empty_relax; trivial.
  Qed.

End ObjectProps.