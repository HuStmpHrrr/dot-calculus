Require Import Definitions.

Reserved Notation "G '⊢#' t '⦂' T" (at level 70, t at level 79).
Reserved Notation "G '⊢#' T '<⦂' U" (at level 70, T at level 79).

Inductive tyt_trm : env -> trm -> typ -> Prop :=
| tyt_var : forall G x T,
    binds x T G ->
    G ⊢# trm_var x ⦂ T
| tyt_all_intro : forall L G T t U,
    (forall x, x `notin` L ->
          x ~ T ++ G ⊢ open x t ⦂ open x U) ->
    G ⊢# trm_val (λ( T ){ t }) ⦂ all( T ) U
| tyt_all_elim : forall G (x z : atom) S T,
    G ⊢# trm_var x ⦂ all( S ) T ->
    G ⊢# trm_var z ⦂ S ->
    G ⊢# (trm_app x z) ⦂ open z T
| tyt_obj_intro : forall L G ds DS,
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x (μ{ DS }) ++ G ⊩[ ds ⦂ DS ]) ->
    wf_defs ds ->
    G ⊢# trm_val (ν( DS ){ ds }) ⦂ μ{ DS }
| typ_obj_elim : forall G x DS a T,
    G ⊢# trm_var x ⦂ μ{ DS } ->
    lbinds (label_trm a) (dec_trm T) DS ->
    G ⊢# trm_sel x a ⦂ T
| tyt_let : forall L G t u T U,
    G ⊢# t ⦂ T ->
    (forall x, x `notin` L ->
          x ~ T ++ G ⊢ open x u ⦂ U) ->
    G ⊢# lett u inn u ⦂ U
| tyt_sub : forall G t T U,
    G ⊢# t ⦂ T ->
    G ⊢# T <⦂ U ->
    G ⊢# t ⦂ U
where "G ⊢# t ⦂ T" := (tyt_trm G t T) : type_scope
with
subtypt : env -> typ -> typ -> Prop :=
| subtypt_top : forall G T,
    G ⊢# T <⦂ ⊤
| subtypt_bot : forall G T,
    G ⊢# ⊥ <⦂ T
| subtypt_refl : forall G T,
    G ⊢# T <⦂ T
| subtypt_trans : forall G S T U,
    G ⊢# S <⦂ T ->
    G ⊢# T <⦂ U ->
    G ⊢# S <⦂ U
| subtypt_all: forall L G S1 T1 S2 T2,
    G ⊢# S2 <⦂ S1 ->
    (forall x, x `notin` L ->
       x ~ S1 ++ G ⊢ open x T1 <⦂ open x T2) ->
    G ⊢# typ_all S1 T1 <⦂ typ_all S2 T2
| subtypt_fld : forall L G a T (DS1 DS2 : decs) U,
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x
            (μ{ append DS1 $ decs_cons (label_trm a) (dec_trm T) DS2 }) ++
            G ⊢ T <⦂ U) ->
    G ⊢# μ{ append DS1 $ decs_cons (label_trm a) (dec_trm T) DS2 }
      <⦂ μ{ append DS1 $ decs_cons (label_trm a) (dec_trm U) DS2 } (* DS[a := U] *)
| subtypt_typ : forall L G A (DS1 DS2 : decs) S1 T1 S2 T2,
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x
            (μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }) ++
            G ⊢ S2 <⦂ S1) ->
    (forall y, y `notin` L ->
          y ~ open_typ_to_context y
            (μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }) ++
            G ⊢ T1 <⦂ T2) ->
    G ⊢# μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }
      <⦂ μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S2 T2) DS2 }
      (* DS[A := S2 .. T2] *)
| subtypt_drop1 : forall G (DS1 : decs) (DS2 : decs),
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢# μ{ append DS1 DS2 } <⦂ μ{ DS2 }
| subtypt_drop2 : forall G (DS1 : decs) (DS2 : decs),
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢# μ{ append DS1 DS2 } <⦂ μ{ DS1 }
| subtypt_merge : forall G (DS : decs) (DS1 : decs) (DS2 : decs),
    not_empty DS ->
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢# μ{ DS } <⦂ μ{ DS1 } ->
    G ⊢# μ{ DS } <⦂ μ{ DS2 } ->
    G ⊢# μ{ DS } <⦂ μ{ append DS1 DS2 }
| subtypt_sel1 : forall G x A DS S T,
    binds x (μ{ DS }) G ->
    lbinds (label_typ A) (dec_typ S T) DS ->
    G ⊢# S <⦂ typ_sel (avar_f x) A
| subtypt_sel2 : forall G x A DS S T,
    binds x (μ{ DS }) G ->
    lbinds (label_typ A) (dec_typ S T) DS ->
    G ⊢# typ_sel (avar_f x) A <⦂ T
where "G ⊢# T <⦂ U" := (subtypt G T U) : type_scope.
Hint Constructors tyt_trm subtypt.


Tactic Notation "tight" "typing" "undec" "1" :=
  match goal with
  | [ |- _ ⊢ _ ⦂ _ ] => econstructor
  | [ |- context[typ_all] ] => eapply subtypt_all
  | [ |- context[dec_trm]] => eapply subtypt_fld
  | [ |- context[dec_typ]] => eapply subtypt_typ
  | [ |- context[ _ ⊢# _ <⦂ _ ⋅ _]] => eapply subtypt_sel1
  | [ |- context[ _ ⊢# _ ⋅ _ <⦂ _]] => eapply subtypt_sel2
  | _ => idtac
  end.

Scheme typt_trm_mut := Induction for tyt_trm Sort Prop
  with subtypt_mut := Induction for subtypt Sort Prop.
Combined Scheme typt_mut from typt_trm_mut, subtypt_mut.


Ltac mut_ind_2 ::=
  match goal with
  | [ |- (forall (G : env) (t : trm) (T : typ) (_ : G ⊢# t ⦂ T), _) /\
        (forall (G0 : env) (S U : typ) (_ : G0 ⊢# S <⦂ U), _) ] =>
    apply typt_mut
  end.


Lemma tight_to_general :
  (forall G t T, G ⊢# t ⦂ T ->
            G ⊢ t ⦂ T) /\
  (forall G S U, G ⊢# S <⦂ U ->
            G ⊢ S <⦂ U).
Proof. mutual induction; eroutine. Qed.