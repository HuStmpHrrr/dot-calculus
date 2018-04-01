
Set Implicit Arguments.

Require Import Definitions.
Require Import LibUtils.
Require Import Coq.Lists.List.

Section ObjectProps.

  Local Hint Resolve not_empty_relax.
  
  Lemma obj_exchg_equiv : forall G (DS1 DS2 : decs),
      not_empty DS1 ->
      not_empty DS2 ->
      G ⊢ μ{ append DS1 DS2 } ≊ μ{ append DS2 DS1 }.
  Proof.
    (routine hinted constructor);
      eroutine hinted rewrite append_sound; reassoc 2 with 0.
  Qed.

End ObjectProps.