Require Import Definitions.

Reserved Notation "[ s1 ] t1 ↦ [ s2 ] t2" (at level 40, t2 at level 39).

Inductive opred : sta -> trm -> sta -> trm -> Prop :=
| red_sel : forall s x a t DS dfs,
    binds x (ν(DS){ dfs }) s ->
    lbinds (label_trm a) (open x $ def_trm t) dfs ->
    [s] (trm_sel x $ a) ↦ [s] t
| red_app : forall s x y T t,
    binds x (λ(T){t}) s ->
    [s] trm_app x (avar_f y) ↦ [s] open y t
| red_let_val : forall s v x t,
    x `notin` dom s ->
    [s] lett (trm_val v) inn t ↦ [(x ~ open_val_to_context x v) ++ s] open x t
| red_let_var : forall s t x,
    [s] lett (trm_var $ avar_f x) inn t ↦ [s] open x t
| red_let_tgt : forall s s' t0 t0' t,
    [s] t0 ↦  [s'] t0' ->
    [s] lett t0 inn t ↦ [s'] lett t0' inn t
where "[ s1 ] t1 ↦ [ s2 ] t2" := (opred s1 t1 s2 t2).
Hint Constructors opred.

Inductive nf : trm -> Prop :=
| nf_var : forall x, nf (trm_var x)
| nf_val : forall v, nf (trm_val v).
Hint Constructors nf.