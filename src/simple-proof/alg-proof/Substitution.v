Set Implicit Arguments.

Require Import Definitions.
Require Import LibUtils.
Require Import Coq.Lists.List.
Require Import Concepts.
Require Import Metalib.Metatheory.

Section SubstDefinitions.

  Variable z u : var.

  Definition subst_avar (a : avar) : avar :=
    match a with
    | avar_b i as a => a
    | avar_f x => avar_f $ if x == z then u else x
    end.

  Fixpoint subst_typ (T : typ) : typ :=
    match T with
    | typ_top => ⊤
    | typ_bot => ⊥
    | typ_sel x L => (subst_avar x) ⋅ L
    | typ_all T U => all( subst_typ T ) subst_typ U
    | typ_obj DS => μ{ subst_decs DS }
    end
  with
  subst_dec (D : dec) : dec :=
    match D with
    | dec_typ T U => dec_typ (subst_typ T) $ subst_typ U
    | dec_trm T => dec_trm $ subst_typ T
    end
  with
  subst_decs (DS : decs) : decs :=
    match DS with
    | decs_nil => decs_nil
    | decs_cons L D DS' => decs_cons L (subst_dec D) $ subst_decs DS'
    end.

  Fixpoint subst_trm (t : trm) : trm :=
    match t with
    | trm_var x => trm_var $ subst_avar x
    | trm_val v => trm_val $ subst_val v
    | trm_sel x L => trm_sel (subst_avar x) L
    | trm_app x1 x2 => trm_app (subst_avar x1) $ subst_avar x2
    | trm_let t1 t2 => trm_let (subst_trm t1) $ subst_trm t2
    end
  with
  subst_val (v : val) : val :=
    match v with
    | ν( DS ){ ds } => ν( subst_decs DS ){ subst_defs ds }
    | λ( T ){ t } => λ( subst_typ T ){ subst_trm t }
    end
  with
  subst_def (d : def) : def :=
    match d with
    | def_typ T => def_typ $ subst_typ T
    | def_trm t => def_trm $ subst_trm t
    end
  with
  subst_defs (ds : defs) : defs :=
    match ds with
    | defs_nil => defs_nil
    | defs_cons L d ds' => defs_cons L (subst_def d) $ subst_defs ds'
    end.

End SubstDefinitions.

Instance SubstAvar : CanSubst avar := { substi := subst_avar }.
Instance SubstTyp : CanSubst typ := { substi := subst_typ }.
Instance SubstDec : CanSubst dec := { substi := subst_dec }.
Instance SubstDecs : CanSubst decs := { substi := subst_decs }.
Instance SubstTrm : CanSubst trm := { substi := subst_trm }.
Instance SubstVal : CanSubst val := { substi := subst_val }.
Instance SubstDef : CanSubst def := { substi := subst_def }.
Instance SubstDefs : CanSubst defs := { substi := subst_defs }.

Section OpenFreshInj.
  
  Variable z : atom.

  Local Notation fresh_inj T :=
    (forall (x y : T) k,
      z `notin` fv x ->
      z `notin` fv y ->
      open_rec k z x = open_rec k z y ->
      x = y).
  
  Lemma open_fresh_inj_avar : fresh_inj avar.
  Proof.
    intros. destruct x, y; routine.
  Qed.

  Local Hint Resolve open_fresh_inj_avar.

  Local Ltac boom :=
    eroutine by 
      (idtac; match goal with
       | [ H : _ = _ _ z ?t' |- _ ] =>
         destruct t'; inversion H
       end).
  
  Lemma open_fresh_inj_typ_dec_decs :
    fresh_inj typ /\ fresh_inj dec /\ fresh_inj decs.
  Proof. mutual induction; boom. Qed.

  Local Hint Extern 1 (_ = _) =>
  match goal with
  | [ |- ?t = _ ] =>
    ensure typ t; eapply open_fresh_inj_typ_dec_decs
  end.
  
  Lemma open_fresh_inj_trm_val_def_defs :
    fresh_inj trm /\ fresh_inj val /\ fresh_inj def /\ fresh_inj defs.
  Proof. mutual induction; boom. Qed.
  
End OpenFreshInj.


Section SubstFresh.
  
  Variable x y : var.

  Local Notation subst_fresh T :=
    (forall t : T, x `notin` fv t -> substi x y t = t).

  Lemma subst_fresh_avar : subst_fresh avar.
  Proof.
    intros. destruct t; routine.
  Qed.

  Local Hint Resolve subst_fresh_avar.

  Lemma subst_fresh_typ_dec_decs :
    subst_fresh typ /\ subst_fresh dec /\ subst_fresh decs.
  Proof. mutual induction; routine. Qed.

  Local Hint Extern 1 (_ = _) =>
  match goal with
  | [ |- ?t = _ ] =>
    ensure typ t; apply subst_fresh_typ_dec_decs
  end.

  Lemma subst_fresh_trm_val_def_defs :
    subst_fresh trm /\ subst_fresh val /\ subst_fresh def /\ subst_fresh defs.
  Proof. mutual induction; routine. Qed.
  
End SubstFresh.


Section SubstOpenComm.

  Variable x y : var.

  (** z[y/x] *)
  Definition subst_fvar (z : var) : var :=
    if z == x then y else z.

  Variable u : var.

  Local Notation subst_open_comm T u :=
    (forall (t : T) (n : nat),
        substi x y (open_rec n u t) =
        open_rec n (subst_fvar u) $ substi x y t).

  Lemma subst_open_comm_avar : forall u,
      subst_open_comm avar u.
  Proof.
    intros. destruct t; routine by (idtac; unfold subst_fvar).
  Qed.

  Local Hint Resolve subst_open_comm_avar.
  
  Lemma subst_open_comm_typ_dec_decs : forall u,
      subst_open_comm typ u /\ subst_open_comm dec u /\
      subst_open_comm decs u.
  Proof. mutual induction; routine. Qed.

  Local Hint Extern 1 =>
  match goal with
  | [  |- ?x = _ ] =>
    ensure typ x; apply subst_open_comm_typ_dec_decs
  end.

  Lemma subst_open_comm_trm_val_def_defs : forall u,
      subst_open_comm trm u /\ subst_open_comm val u /\
      subst_open_comm def u /\ subst_open_comm defs u.
  Proof. mutual induction; routine. Qed.

End SubstOpenComm.
Hint Unfold subst_fvar.

Section SubstIntro.

  Local Notation subst_intro T :=
    (forall x u (t : T) (n : nat), x `notin` fv t ->
                            open_rec n u t = substi x u $ open_rec n x t).
  
  Local Hint Extern 1 => exrewrite subst_fresh_typ_dec_decs.

  Local Hint Extern 1 => exrewrite subst_fresh_trm_val_def_defs.

  Local Ltac boom :=
    routine by (exrewrite (conj subst_open_comm_trm_val_def_defs
                                subst_open_comm_typ_dec_decs)).
  
  Lemma subst_intro_trm : subst_intro trm.
  Proof. boom. Qed.

  Lemma subst_intro_defs : subst_intro defs.
  Proof. boom. Qed.

  Lemma subst_intro_def : subst_intro def.
  Proof. boom. Qed.

  Lemma subst_intro_typ : subst_intro typ.
  Proof. boom. Qed.

End SubstIntro.
