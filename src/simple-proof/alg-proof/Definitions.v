(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    Coq library by Arthur Chargueraud. *)

Set Implicit Arguments.

Require Export Metalib.Metatheory.
(* Require LibLN. *)
Require Export LibUtils.
Require Export Concepts.
Require Import Coq.Lists.List.


Inductive avar : Set :=
| avar_b : nat -> avar
| avar_f : var -> avar.

Hint Constructors avar.

Coercion avar_b : nat >-> avar.
Coercion avar_f : var >-> avar.


Inductive typ : Set :=
| typ_top : typ
| typ_bot : typ
| typ_sel : avar -> typ_label -> typ
| typ_all : typ -> typ -> typ
| typ_obj : decs -> typ
with
dec : Set :=
(** dec_typ X A B ::= X : A .. B *)
| dec_typ : typ -> typ -> dec
(** dec_trm x T ::= x : T *)
| dec_trm : typ -> dec
with
decs : Set :=
| decs_nil : decs
| decs_cons : label -> dec -> decs -> decs.

Hint Constructors typ dec decs.


Fixpoint decs_to_list (DS : decs) :=
  match DS with
  | decs_nil => nil
  | decs_cons l d DS' => (l, d) :: decs_to_list DS'
  end.

Fixpoint decs_from_list (l : list (label * dec)) :=
  match l with
  | nil => decs_nil
  | cons (l, d) l' => decs_cons l d $ decs_from_list l'
  end.

Fixpoint decs_append (DS1 : decs) (DS2 : decs) : decs :=
  match DS1 with
  | decs_nil => DS2
  | decs_cons l D DS1' => decs_cons l D $ decs_append DS1' DS2
  end.

Instance DecsList : ListIso (label * dec) decs :=
  {
    to_list := decs_to_list;
    from_list := decs_from_list;
    append := decs_append
  }.
Proof.
  all:induction on decs || induction on list; routine.
Qed.

Coercion decs_to_list : decs >-> list.

Notation "⊤" := typ_top.
Notation "⊥" := typ_bot.
Notation "x ⋅ T" := (typ_sel x T) (at level 40).
Notation "all( A ) B" := (typ_all A B) (at level 40).

Notation "X ∈ A ⋯ B" := (X, dec_typ A B) (at level 40).
Notation "x ∷ T" := (x, dec_trm T) (at level 40).
Notation "μ{ ds }" := (typ_obj ds) (at level 40).

Section TypExample.
  Variable X : nat.
  Variable Y : nat.
  Check μ{ from_list $ <[ label_trm X ∷ ⊥ ; label_typ Y ∈ ⊥ ⋯ ⊤ ]> }.
End TypExample.


Inductive wf_lab_dec : label * dec -> Prop :=
| wf_ld_typ : forall X A B, wf_lab_dec (label_typ X ∈ A ⋯ B)
| wf_ld_trm : forall x T, wf_lab_dec (label_trm x ∷ T).
Hint Constructors wf_lab_dec.

Definition wf_decs (l : decs) := not_empty l /\ Forall wf_lab_dec l.
Hint Unfold wf_decs.
Hint Transparent wf_decs.

Inductive trm : Set :=
| trm_var : avar -> trm
| trm_val : val -> trm
| trm_sel : avar -> trm_label -> trm
| trm_app : avar -> avar -> trm
| trm_let : trm -> trm -> trm
with
val : Set :=
| val_new : decs -> defs -> val
| val_lambda : typ -> trm -> val
with
def : Set :=
| def_typ : typ -> def
| def_trm : trm -> def
with
defs : Set :=
| defs_nil : defs
| defs_cons : label -> def -> defs -> defs.

Hint Constructors trm val def defs.

Fixpoint defs_to_list (DS : defs) :=
  match DS with
  | defs_nil => nil
  | defs_cons l d DS' => (l, d) :: defs_to_list DS'
  end.

Fixpoint defs_from_list (l : list (label * def)) :=
  match l with
  | nil => defs_nil
  | cons (l, d) l' => defs_cons l d $ defs_from_list l'
  end.

Fixpoint defs_append (DS1 : defs) (DS2 : defs) : defs :=
  match DS1 with
  | defs_nil => DS2
  | defs_cons l D DS1' => defs_cons l D $ defs_append DS1' DS2
  end.

Instance DefsList : ListIso (label * def) defs :=
  {
    to_list := defs_to_list;
    from_list := defs_from_list;
    append := defs_append
  }.
Proof.
  all:induction on defs || induction on list; routine.
Qed.

Coercion defs_to_list : defs >-> list.

Notation "'lett' x 'inn' y" := (trm_let x y) (at level 40).

Notation "A ≡ B" := (A, def_typ B) (at level 40).
Notation "x ⩴ t" := (x, def_trm t) (at level 40).

Notation "ν( DS ){ ds }" := (val_new DS ds) (at level 40).

Notation "λ( T ){ t }" := (val_lambda T t) (at level 40).

Inductive wf_lab_def : label * def -> Prop :=
| wf_lf_typ : forall A B, wf_lab_def (label_typ A ≡ B)
| wf_lf_trm : forall x t, wf_lab_def (label_trm x ⩴ t).
Hint Constructors wf_lab_def.

Definition wf_defs (l : defs) := luniq l /\ not_empty l /\ Forall wf_lab_def l.
Hint Unfold wf_defs.
Hint Transparent wf_defs.


(** OPENING *)
Section OpeningDefinition.
  
  Definition open_rec_avar (k : nat) (u : var) (a : avar) : avar :=
    match a with
    | avar_b i => if k == i then avar_f u else avar_b i
    | avar_f x => avar_f x
    end.

  Fixpoint open_rec_typ (k : nat) (u : var) (T : typ) : typ :=
    match T with
    | ⊤ => ⊤
    | ⊥ => ⊥
    | x ⋅ T => (open_rec_avar k u x) ⋅ T
    | all( T ) U => all( open_rec_typ k u T ) open_rec_typ (S k) u U
    | μ{ ds } => μ{ open_rec_decs (S k) u ds }
    end
  with
  open_rec_dec (k : nat) (u : var) (D : dec) : dec :=
    match D with
    | dec_typ T U => dec_typ (open_rec_typ k u T) $ open_rec_typ k u U
    | dec_trm T => dec_trm $ open_rec_typ k u T
    end
  with
  open_rec_decs (k : nat) (u : var) (DS : decs) : decs :=
    match DS with
    | decs_nil => decs_nil
    | decs_cons l D DS' =>
      decs_cons l (open_rec_dec k u D) $ open_rec_decs k u DS'
    end.
  
  (**
   * we need this function in order to open an object by its own.
   *)
  Definition open_typ_to_context (u : var) (T : typ) : typ :=
    match T with
    | μ{ ds } => μ{ open_rec_decs 0 u ds }
    | T => open_rec_typ 0 u T
    end.

  
  Fixpoint open_rec_trm (k : nat) (u : var) (t : trm) : trm :=
    match t with
    | trm_var a => trm_var $ open_rec_avar k u a
    | trm_val v => trm_val $ open_rec_val k u v
    | trm_sel v m => trm_sel (open_rec_avar k u v) m
    | trm_app f x => trm_app (open_rec_avar k u f) $ open_rec_avar k u x
    | trm_let t1 t2 => trm_let (open_rec_trm k u t1) $ open_rec_trm (S k) u t2
    end
  with
  open_rec_val (k : nat) (u : var) (v : val) : val :=
    match v with
    | λ( T ){ e } => λ( open_rec_typ k u T ){ open_rec_trm (S k) u e }
    | ν( DS ){ ds } =>
      ν( open_rec_decs (S k) u DS ){ open_rec_defs (S k) u ds }
    end
  with
  open_rec_def (k : nat) (u : var) (d : def) : def :=
    match d with
    | def_typ T => def_typ $ open_rec_typ k u T
    | def_trm e => def_trm $ open_rec_trm k u e
    end
  with
  open_rec_defs (k : nat) (u : var) (ds : defs) : defs :=
    match ds with
    | defs_nil => defs_nil
    | defs_cons l df ds' => defs_cons l (open_rec_def k u df) $ open_rec_defs k u ds'
    end.

  Definition open_val_to_context (u : var) (v : val) : val :=
    match v with
    | ν( DS ){ ds } => ν( open_rec_decs 0 u DS ){ open_rec_defs 0 u ds }
    | v => open_rec_val 0 u v
    end.

  Definition open_trm_to_context (u : var) (t : trm) : trm :=
    match t with
    | trm_val v => trm_val $ open_val_to_context u v
    | t => open_rec_trm 0 u t
    end.
  
End OpeningDefinition.

Instance OpenAvar : CanOpen avar := { open_rec := open_rec_avar }.
Instance OpenTyp : CanOpen typ := { open_rec := open_rec_typ }.
Instance OpenDec : CanOpen dec := { open_rec := open_rec_dec }.
Instance OpenDecs : CanOpen decs := { open_rec := open_rec_decs }.
Instance OpenTrm : CanOpen trm := { open_rec := open_rec_trm }.
Instance OpenVal : CanOpen val := { open_rec := open_rec_val }.
Instance OpenDef : CanOpen def := { open_rec := open_rec_def }.
Instance OpenDefs : CanOpen defs := { open_rec := open_rec_defs }.

Notation open := (open_rec 0).


Section FreeVariables.

  Definition fv_avar (a : avar) : atoms :=
    match a with
    | avar_b i => {}
    | avar_f x => {{ x }}
    end.

  Fixpoint fv_typ (T : typ) : atoms :=
    match T with
    | ⊤ => {}
    | ⊥ => {}
    | x ⋅ T => fv_avar x
    | all( T ) U => fv_typ T `union` fv_typ U
    | μ{ DS } => fv_decs DS
    end
  with
  fv_dec (D : dec) : atoms :=
    match D with
    | dec_typ T U => fv_typ T `union` fv_typ U
    | dec_trm T => fv_typ T
    end
  with
  fv_decs (DS : decs) : atoms :=
    match DS with
    | decs_nil => {}
    | decs_cons _ D DS' => fv_dec D `union` fv_decs DS'
    end.

  Fixpoint fv_trm (t : trm) : atoms :=
    match t with
    | trm_var a => fv_avar a
    | trm_val v => fv_val v
    | trm_sel v m => fv_avar v
    | trm_app f x => fv_avar f `union` fv_avar x
    | trm_let t1 t2 => fv_trm t1 `union` fv_trm t2
    end
  with
  fv_val (v : val) : atoms :=
    match v with
    | λ( T ){ e } => fv_typ T `union` fv_trm e
    | ν( DS ){ ds } => fv_decs DS `union` fv_defs ds
    end
  with
  fv_def (d : def) : atoms :=
    match d with
    | def_typ T => fv_typ T
    | def_trm e => fv_trm e
    end
  with
  fv_defs (ds : defs) : atoms :=
    match ds with
    | defs_nil => {}
    | defs_cons _ d ds' => fv_def d `union` fv_defs ds'
    end.

End FreeVariables.

Instance FvAvar : HasFv avar := { fv := fv_avar }.
Instance FvTyp : HasFv typ := { fv := fv_typ }. 
Instance FvDec : HasFv dec := { fv := fv_dec }. 
Instance FvDecs : HasFv decs := { fv := fv_decs }.
Instance FvTrm : HasFv trm := { fv := fv_trm }.
Instance FvVal : HasFv val := { fv := fv_val }.
Instance FvDef : HasFv def := { fv := fv_def }.
Instance FvDefs : HasFv defs := { fv := fv_defs }.

Notation env := (list (atom * typ)).
Notation sta := (list (atom * val)).

Definition fv_values {T : Type} (f : T -> atoms)
           (l : list (atom * T)) : atoms :=
  fold_right (fun (b : (atom * T)) a =>
               a `union` let (_, t) := b in f t) {} l.

Instance FvEnv : HasFv env := { fv := fv_values fv }.
Instance FvSta : HasFv sta := { fv := fv_values fv }.


Reserved Notation "G '⊢' t '⦂' T" (at level 70, t at level 79).
Reserved Notation "G '⊢' T '<⦂' U" (at level 70, T at level 79).
Reserved Notation "G ⊩ d ⦂ D" (at level 70, d at level 79).
Reserved Notation "G ⊩[ ds ⦂ DS ]" (at level 70, ds at level 79).

Inductive ty_trm : env -> trm -> typ -> Prop :=
| ty_var : forall G x T,
    binds x T G ->
    G ⊢ trm_var x ⦂ T
| ty_all_intro : forall L G T t U,
    (forall x, x `notin` L ->
          x ~ T ++ G ⊢ open x t ⦂ open x U) ->
    G ⊢ trm_val (λ( T ){ t }) ⦂ all( T ) U
| ty_all_elim : forall G (x z : atom) S T,
    G ⊢ trm_var x ⦂ all( S ) T ->
    G ⊢ trm_var z ⦂ S ->
    G ⊢ (trm_app x z) ⦂ open z T
| ty_obj_intro : forall L G ds DS,
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x (μ{ DS }) ++ G ⊩[ ds ⦂ DS ]) ->
    wf_defs ds ->
    G ⊢ trm_val (ν( DS ){ ds }) ⦂ μ{ DS }
| typ_obj_elim : forall G x DS a T,
    G ⊢ trm_var x ⦂ μ{ DS } ->
    lbinds (label_trm a) (dec_trm T) DS ->
    G ⊢ trm_sel x a ⦂ T
| ty_let : forall L G t u T U,
    G ⊢ t ⦂ T ->
    (forall x, x `notin` L ->
          x ~ T ++ G ⊢ open x u ⦂ U) ->
    G ⊢ lett u inn u ⦂ U
| ty_sub : forall G t T U,
    G ⊢ t ⦂ T ->
    G ⊢ T <⦂ U ->
    G ⊢ t ⦂ U
where "G ⊢ t ⦂ T" := (ty_trm G t T) : type_scope
with
ty_def : env -> (label * def) -> dec -> Prop :=
| ty_def_typ : forall G A T,
    G ⊩ (label_typ A, def_typ T) ⦂ dec_typ T T
| ty_def_trm : forall G a t T,
    G ⊢ t ⦂ T ->
    G ⊩ (label_trm a, def_trm t) ⦂ dec_trm T
where "G ⊩ d ⦂ D" := (ty_def G d D) : type_scope
with
ty_defs : env -> defs -> decs -> Prop :=
| ty_defs_single : forall G l d D,
    G ⊩ (l, d) ⦂ D ->
    G ⊩[ defs_cons l d defs_nil ⦂ decs_cons l D decs_nil ]
| ty_defs_mult : forall G l d D ds DS,
    G ⊩ (l, d) ⦂ D ->
    G ⊩[ ds ⦂ DS ] ->
    G ⊩[ defs_cons l d ds ⦂ decs_cons l D DS ]
where "G ⊩[ ds ⦂ DS ]" := (ty_defs G ds DS) : type_scope
with
subtyp : env -> typ -> typ -> Prop :=
| subtyp_top : forall G T,
    G ⊢ T <⦂ ⊤
| subtyp_bot : forall G T,
    G ⊢ ⊥ <⦂ T
| subtyp_refl : forall G T,
    G ⊢ T <⦂ T
| subtyp_trans : forall G S T U,
    G ⊢ S <⦂ T ->
    G ⊢ T <⦂ U ->
    G ⊢ S <⦂ U
| subtyp_all: forall L G S1 T1 S2 T2,
    G ⊢ S2 <⦂ S1 ->
    (forall x, x `notin` L ->
       x ~ S1 ++ G ⊢ open x T1 <⦂ open x T2) ->
    G ⊢ all(S1) T1 <⦂ all(S2) T2
| subtyp_fld : forall L G a T (DS1 DS2 : decs) U,
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x
            (μ{ append DS1 $ decs_cons (label_trm a) (dec_trm T) DS2 }) ++
            G ⊢ T <⦂ U) ->
    G ⊢ μ{ append DS1 $ decs_cons (label_trm a) (dec_trm T) DS2 }
      <⦂ μ{ append DS1 $ decs_cons (label_trm a) (dec_trm U) DS2 } (* DS[a := U] *)
| subtyp_typ : forall L G A (DS1 DS2 : decs) S1 T1 S2 T2,
    (forall x, x `notin` L ->
          x ~ open_typ_to_context x
            (μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }) ++
            G ⊢ S2 <⦂ S1) ->
    (forall y, y `notin` L ->
          y ~ open_typ_to_context y
            (μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }) ++
            G ⊢ T1 <⦂ T2) ->
    G ⊢ μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S1 T1) DS2 }
      <⦂ μ{ append DS1 $ decs_cons (label_typ A) (dec_typ S2 T2) DS2 }
      (* DS[A := S2 .. T2] *)
| subtyp_drop1 : forall G (DS1 : decs) (DS2 : decs),
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢ μ{ append DS1 DS2 } <⦂ μ{ DS2 }
| subtyp_drop2 : forall G (DS1 : decs) (DS2 : decs),
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢ μ{ append DS1 DS2 } <⦂ μ{ DS1 }
| subtyp_merge : forall G (DS : decs) (DS1 : decs) (DS2 : decs),
    not_empty DS ->
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢ μ{ DS } <⦂ μ{ DS1 } ->
    G ⊢ μ{ DS } <⦂ μ{ DS2 } ->
    G ⊢ μ{ DS } <⦂ μ{ append DS1 DS2 }
| subtyp_sel1 : forall G x A DS S T,
    G ⊢ trm_var x ⦂ μ{ DS } ->
    lbinds (label_typ A) (dec_typ S T) DS ->
    G ⊢ S <⦂ typ_sel x A
| subtyp_sel2 : forall G x A DS S T,
    G ⊢ trm_var x ⦂ μ{ DS } ->
    lbinds (label_typ A) (dec_typ S T) DS ->
    G ⊢ typ_sel x A <⦂ T
where "G ⊢ T <⦂ U" := (subtyp G T U) : type_scope.
Hint Constructors ty_trm ty_def ty_defs subtyp.


Definition ty_equivalence G T U : Prop :=
  G ⊢ T <⦂ U <-> G ⊢ U <⦂ T.

Notation "G ⊢ T ≊ U" :=
  (ty_equivalence G T U)(at level 70, T at level 79) : type_scope.


(** mutual inductive schemes *)

Scheme typ_mut := Induction for typ Sort Prop
  with dec_mut := Induction for dec Sort Prop
  with decs_mut := Induction for decs Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut, decs_mut.


Scheme trm_mut := Induction for trm Sort Prop
  with val_mut := Induction for val Sort Prop
  with def_mut := Induction for def Sort Prop
  with defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ty_trm_mut := Induction for ty_trm Sort Prop
  with ty_def_mut := Induction for ty_def Sort Prop
  with ty_defs_mut := Induction for ty_defs Sort Prop
  with subtyp_mut := Induction for subtyp Sort Prop.
Combined Scheme typing_mut from ty_trm_mut, ty_def_mut, ty_defs_mut, subtyp_mut.

(** Tactics *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : env => dom x `union` fv x) in
  let D := gather_atoms_with fv_avar in
  let E := gather_atoms_with fv_typ in
  let F := gather_atoms_with fv_dec in
  let G := gather_atoms_with fv_decs in
  let H := gather_atoms_with fv_trm in
  let I := gather_atoms_with fv_val in
  let J := gather_atoms_with fv_def in
  let K := gather_atoms_with fv_defs in
  let L := gather_atoms_with (fun x : sta => dom x `union` fv x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G
            `union` H `union` I `union` J `union` K `union` L).


(** hook for mutual induction tactic *)
Ltac mut_ind_2 := fail.

Ltac mut_ind :=
  intros;
  match goal with
  | [ |- (forall _ : typ, _) /\ (forall _ : dec, _) /\ (forall _ : decs, _) ] =>
    apply typ_mutind
  | [ |- (forall _ : trm, _) /\ (forall _ : val, _) /\ (forall _ : def, _) /\ (forall _ : defs, _)] =>
    apply trm_mutind
  | [ |- (forall (G : env) (t : trm) (T : typ) (_ : G ⊢ t ⦂ T), _) /\
        (forall (G0 : env) (d : (label * def)) (D : dec)
           (_ : G0 ⊩ d ⦂ D), _) /\
        (forall (G1 : env) (dfs : defs) (DS : decs)
           (_ : G1 ⊩[ dfs ⦂ DS ]), _) /\
        (forall (G2 : env) (S U : typ) (_ : G2 ⊢ S <⦂ U), _) ] =>
    apply typing_mut
  end || mut_ind_2.

Tactic Notation "mutual" "induction" := mut_ind.
Tactic Notation "mutual" "induction*" := mutual induction; intros.

Tactic Notation "ensure" "typ" constr(t) :=
  match type of t with
  | typ => idtac
  | dec => idtac
  | decs => idtac
  end.

Tactic Notation "ensure" "trm" constr(t) :=
  match type of t with
  | trm => idtac
  | val => idtac
  | def => idtac
  | defs => idtac
  end.

(** The first kind of undecidability for typing. see if we can hit more. *)
Tactic Notation "typing" "undec" "1" :=
  match goal with
  | [ |- _ ⊢ _ ⦂ _ ] => econstructor
  | [ |- context[typ_all] ] => eapply subtyp_all
  | [ |- context[dec_trm]] => eapply subtyp_fld
  | [ |- context[dec_typ]] => eapply subtyp_typ
  | [ |- context[ _ ⊢ _ <⦂ _ ⋅ _]] => eapply subtyp_sel1
  | [ |- context[ _ ⊢ _ ⋅ _ <⦂ _]] => eapply subtyp_sel2
  | _ => idtac
  end.