Require Import Metalib.Metatheory.


Class CanOpen (A : Type) :=
  {
    open_rec (k : nat) (u : var) (ins : A) : A
  }.
Hint Unfold open_rec.

Class HasFv (A : Type) :=
  {
    fv (ins : A) : atoms
  }.
Hint Unfold fv.

Class CanSubst (A : Type) :=
  {
    substi (z u : var) (ins : A) : A
  }.
Hint Unfold substi.