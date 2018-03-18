(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    Coq library by Arthur Chargueraud. *)

Set Implicit Arguments.

(* Require Import LibLN. *)
Require Import SyntaxAndTactics.
Require Import Metalib.Metatheory.
Require Import LibUtils.

Require Import Coq.Lists.List.


Inductive avar : Set :=
| avar_b : nat -> avar
| avar_f : var -> avar.

Hint Constructors avar : alg_def.

Coercion avar_b : nat >-> avar.
Coercion avar_f : var >-> avar.


Inductive typ : Set :=
| typ_top : typ
| typ_bot : typ
| typ_sel : avar -> typ_label -> typ
| typ_all : typ -> typ -> typ
| typ_obj : list (label * dec) -> typ
with
dec : Set :=
(** dec_typ X A B ::= X : A .. B *)
| dec_typ : typ -> typ -> dec
(** dec_trm x T ::= x : T *)
| dec_trm : typ -> dec.

Hint Constructors typ dec : alg_def.

Notation "⊤" := typ_top.
Notation "⊥" := typ_bot.
Notation "x ⋅ T" := (typ_sel x T) (at level 40).
Notation "all( A ) B" := (typ_all A B) (at level 40).

Notation "X ∈ A ⋯ B" := (X, dec_typ A B) (at level 40).
Notation "x ∷ T" := (x, dec_trm T) (at level 40).
Notation "μ{ ds }" := (typ_obj ds) (at level 40).

(* Parameter X : nat. *)
(* Parameter Y : nat. *)
(* Check μ{ <[ label_trm X ∷ ⊥ ; label_typ Y ∈ ⊥ ⋯ ⊤ ]> }. *)

Inductive wf_lab_dec : label * dec -> Prop :=
| wf_ld_typ : forall X A B, wf_lab_dec (label_typ X ∈ A ⋯ B)
| wf_ld_trm : forall x T, wf_lab_dec (label_trm x ∷ T).
Hint Constructors wf_lab_dec : alg_def.

Definition wf_decs l := not_empty l /\ list_pred wf_lab_dec l.
Hint Unfold wf_decs.

Inductive trm : Set :=
| trm_var : avar -> trm
| trm_val : val -> trm
| trm_sel : avar -> trm_label -> trm
| trm_app : avar -> avar -> trm
| trm_let : trm -> trm -> trm
with
val : Set :=
| val_new : list (label * dec) -> list (label * def) -> val
| val_lambda : typ -> trm -> val
with
def : Set :=
| def_typ : typ -> def
| def_trm : trm -> def.

Hint Constructors trm val def : alg_def.

Notation "'lett' x 'inn' y" := (trm_let x y) (at level 40).

Notation "A ≡ B" := (A, def_typ B) (at level 40).
Notation "x ⩴ t" := (x, def_trm t) (at level 40).

Notation "ν( ds ){ dfs }" := (val_new ds dfs) (at level 40).

Notation "λ( T ){ t }" := (val_lambda T t) (at level 40).

Inductive wf_lab_def : label * def -> Prop :=
| wf_lf_typ : forall A B, wf_lab_def (label_typ A ≡ B)
| wf_lf_trm : forall x t, wf_lab_def (label_trm x ⩴ t).
Hint Constructors wf_lab_def : alg_def.

Definition wf_defs l := LabelAssocList.uniq l /\ not_empty l /\ list_pred wf_lab_def l.
Hint Unfold wf_defs.

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
  | μ{ ds } =>
    let decs_rec := fix decs_rec (DS : list (label * dec)) : list (label * dec) :=
                    match DS with
                    | nil => nil
                    | (l, D) :: DS' =>
                      (l, (open_rec_dec (S k) u D)) :: decs_rec DS'
                    end
    in μ{ decs_rec ds }
  end
with
open_rec_dec (k : nat) (u : var) (D : dec) : dec :=
  match D with
  | dec_typ T U => dec_typ (open_rec_typ k u T) $ open_rec_typ k u U
  | dec_trm T => dec_trm $ open_rec_typ k u T
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
  | ν( DS ){ dfs } =>
    let defs_rec := fix defs_rec (dfs : list (label * def)) : list (label * def) :=
                    match dfs with
                    | nil => nil
                    | (l, df) :: dfs =>
                      (l, open_rec_def (S k) u df) :: defs_rec dfs
                    end
    in ν( LabelAssocList.map (fun d : dec =>
                          open_rec_dec (S k) u d) DS ){
          defs_rec dfs }
  end
with
open_rec_def (k : nat) (u : var) (d : def) : def :=
  match d with
  | def_typ T => def_typ $ open_rec_typ k u T
  | def_trm e => def_trm $ open_rec_trm k u e
  end.

Notation open_avar := (open_rec_avar 0).
Notation open_typ := (open_rec_typ 0).
Notation open_dec := (open_rec_dec 0).
Notation open_trm := (open_rec_trm 0).
Notation open_val := (open_rec_val 0).
Notation open_def := (open_rec_def 0).

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
  | μ{ ds } =>
    let decs_rec := fix decs_rec (DS : list (label * dec)) : atoms :=
                    match DS with
                    | nil => {}
                    | (_, D) :: DS' => fv_dec D `union` decs_rec DS'
                    end
    in decs_rec ds
  end
with
fv_dec (D : dec) : atoms :=
  match D with
  | dec_typ T U => fv_typ T `union` fv_typ U
  | dec_trm T => fv_typ T
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
  | ν( DS ){ dfs } =>
    let defs_rec := fix defs_rec (dfs : list (label * def)) : atoms :=
                    match dfs with
                    | nil => {}
                    | (_, df) :: dfs => fv_def df `union` defs_rec dfs
                    end
    in fold_left AtomSetImpl.union
                 (map (fun t : (label * dec) => let (_, d) := t in fv_dec d) DS)
                 {} `union` defs_rec dfs
  end
with
fv_def (d : def) : atoms :=
  match d with
  | def_typ T => fv_typ T
  | def_trm e => fv_trm e
  end.


Reserved Notation "G '⊢' t '⦂' T" (at level 70, t at level 79).
Reserved Notation "G '⊢' T '<⦂' U" (at level 70, T at level 79).
Reserved Notation "G '⊩' d ⦂ D" (at level 70, d at level 79).
Reserved Notation "G ⊩[ ds ⦂ DS ]" (at level 70, ds at level 79).

Notation env := (list (atom * typ)).

Inductive ty_trm : env -> trm -> typ -> Prop :=
| ty_var : forall G x T,
    binds x T G ->
    G ⊢ trm_var x ⦂ T
| ty_all_intro : forall L G T t U,
    (forall x, x `notin` L ->
          x ~ T ++ G ⊢ open_trm x t ⦂ open_typ x U) ->
    G ⊢ (trm_val $ λ( T ){ t }) ⦂ all( T ) U
| ty_all_elim : forall G (x z : atom) S T,
    G ⊢ trm_var x ⦂ all( S ) T ->
    G ⊢ trm_var z ⦂ S ->
    G ⊢ (trm_app x z) ⦂ open_typ z T
| ty_obj_intro : forall L G ds DS,
    (forall x, x `notin` L ->
          x ~ open_typ x (μ{ DS }) ++ G ⊩[ ds ⦂ DS ]) ->
    wf_defs ds ->
    G ⊢ trm_val (ν( DS ){ ds }) ⦂ μ{ DS }
| typ_obj_elim : forall G x DS a T,
    G ⊢ trm_var x ⦂ μ{ label_trm a ∷ T :: DS } ->
    G ⊢ trm_sel x a ⦂ T
| ty_let : forall L G t u T U,
    G ⊢ t ⦂ T ->
    (forall x, x `notin` L ->
          x ~ T ++ G ⊢ open_trm x u ⦂ U) ->
    G ⊢ lett u inn u ⦂ U
| ty_sub : forall G t T U,
    G ⊢ t ⦂ T ->
    G ⊢ T <⦂ U ->
    G ⊢ t ⦂ U
where "G ⊢ t ⦂ T" := (ty_trm G t T) : type_scope
with
ty_def : env -> label * def -> label * dec -> Prop :=
| ty_def_typ : forall G A T,
    G ⊩ label_typ A ≡ T ⦂ label_typ A ∈ T ⋯ T
| ty_def_trm : forall G a t T,
    G ⊢ t ⦂ T ->
    G ⊩ label_trm a ⩴ t ⦂ label_trm a ∷ T
where "G ⊩ d ⦂ D" := (ty_def G d D) : type_scope
with
ty_defs : env -> list (label * def) -> list (label * dec) -> Prop :=
| ty_defs_single : forall G d D,
    G ⊩ d ⦂ D ->
    G ⊩[ d :: nil ⦂ D :: nil ]
| ty_defs_mult : forall G d D ds DS,
    G ⊩ d ⦂ D ->
    G ⊩[ ds ⦂ DS ] ->
    G ⊩[ d :: ds ⦂ D :: DS ]
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
    (forall x, x \notin L ->
       x ~ S2 ++ G ⊢ open_typ x T1 <⦂ open_typ x T2) ->
    G ⊢ typ_all S1 T1 <⦂ typ_all S2 T2
| subtyp_fld : forall G L a T DS U,
    (forall x, x `notin` L ->
          x ~ open_typ x (μ{ a ∷ T :: DS }) ++ G ⊢ T <⦂ U) ->
    G ⊢ μ{ a ∷ T :: DS } <⦂ μ{ a ∷ U :: DS } (* DS[a := U] *)
| subtyp_typ : forall G L A DS S1 T1 S2 T2,
    (forall x, x `notin` L ->
          x ~ open_typ x (μ{ A ∈ S1 ⋯ T1 :: DS }) ++ G ⊢ S2 <⦂ S1) ->
    (forall y, y `notin` L ->
          y ~ open_typ y (μ{ A ∈ S1 ⋯ T1 :: DS }) ++ G ⊢ T1 <⦂ T2) ->
    G ⊢ μ{ A ∈ S1 ⋯ T1 :: DS } <⦂ μ{ A ∈ S2 ⋯ T2 :: DS } (* DS[A := S2 .. T2] *)
| subtyp_drop1 : forall G DS1 DS2,
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢ μ{ DS1 ++ DS2 } <⦂ μ{ DS2 }
| subtyp_drop2 : forall G DS1 DS2,
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢ μ{ DS1 ++ DS2 } <⦂ μ{ DS1 }
| subtyp_merge : forall G DS DS1 DS2,
    not_empty DS ->
    not_empty DS1 ->
    not_empty DS2 ->
    G ⊢ μ{ DS } <⦂ μ{ DS1 } ->
    G ⊢ μ{ DS } <⦂ μ{ DS2 } ->
    G ⊢ μ{ DS } <⦂ μ{ DS1 ++ DS2 }
| subtyp_sel1 : forall G x A DS S T,
    G ⊢ trm_var x ⦂ μ{ label_typ A ∈ S ⋯ T :: DS } ->
    G ⊢ typ_sel x A <⦂ T
| subtyp_sel2 : forall G x A DS S T,
    G ⊢ trm_var x ⦂ μ{ label_typ A ∈ S ⋯ T :: DS } ->
    G ⊢ S <⦂ typ_sel x A
where "G ⊢ T <⦂ U" := (subtyp G T U) : type_scope.
    
