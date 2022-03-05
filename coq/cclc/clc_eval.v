From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness.

Definition env T := seq (nat * T).

Fixpoint free0 {T} (e : env T) (l : nat) : env T :=
  match e with
  | nil => nil
  | (addr, m) :: e =>
    if l == addr then e else (addr, m) :: free0 e l
  end.

Definition free {T} (e : env T) (l : nat) (t : sort) := 
  match t with
  | U => e
  | L => free0 e l
  end.

Inductive open {T} : env T -> nat -> Prop :=
| open_nil l : 
  open nil l
| open_cons e l addr m :
  open e l ->
  l <> addr ->
  open ((addr, m) :: e) l.

Inductive mapsto {T} : env T -> nat -> T -> Prop :=
| mapsto0 e l m :
  mapsto ((l, m) :: e) l m
| mapsto1 e l addr m n :
  mapsto e l m ->
  mapsto ((addr, n) :: e) l m.

Inductive eterm :=
| eVar    (x : var)
| eLab    (l : nat)
| eSort   (s : sort) (l : nat)
| ePi     (A : eterm) (B : {bind eterm}) (s t : sort)
| eLam    (A : eterm) (B : {bind eterm}) (s t : sort)
| eApp    (m n : eterm)
| eUnit
| eIt
| eSigma  (A : eterm) (B : {bind eterm}) (s r t : sort)
| ePair   (m n : eterm)
| eLetIn1 (m n : eterm)
| eLetIn2 (m n : eterm).

Instance Ids_eterm : Ids eterm. derive. Defined.
Instance Rename_eterm : Rename eterm. derive. Defined.
Instance Subst_eterm : Subst eterm. derive. Defined.
Instance substLemmas_eterm : SubstLemmas eterm. derive. Qed.

Fixpoint embed (tm : term) : eterm :=
  match tm with
  | Var x => eVar x
  | Sort s l => eSort s l
  | Pi A B s t => ePi (embed A) (embed B) s t
  | Lam A m s t => eLam (embed A) (embed m) s t
  | App m n => eApp (embed m) (embed n)
  | Unit => eUnit
  | It => eIt
  | Sigma A B s r t => eSigma (embed A) (embed B) s r t
  | Pair m n => ePair (embed m) (embed n)
  | LetIn1 m n => eLetIn1 (embed m) (embed n)
  | LetIn2 m n => eLetIn2 (embed m) (embed n)
  end.
Notation "[[ m ]]" := (embed m).

Reserved Notation "Θ ;; m => Θ' ;; n" 
  (at level 80, m, Θ', n at next level).

Inductive eval : env eterm -> eterm -> env eterm -> eterm -> Prop :=
| eval_sort Θ s i l :
  open Θ l ->
  Θ ;; eSort s i => (l, eSort s i) :: Θ ;; eLab l
| eval_pi Θ A B s t l :
  open Θ l ->
  Θ ;; ePi A B s t => (l, ePi A B s t) :: Θ ;; eLab l
| eval_lam Θ A m s t l :
  open Θ l ->
  Θ ;; eLam A m s t => (l, eLam A m s t) :: Θ ;; eLab l
| eval_appL Θ Θ' m m' n :
  Θ ;; m => Θ' ;; m' ->
  Θ ;; eApp m n => Θ' ;; eApp m' n
| eval_appR Θ Θ' l n n' :
  Θ ;; n => Θ' ;; n' ->
  Θ ;; eApp (eLab l) n => Θ' ;; eApp (eLab l) n'
| eval_beta Θ Θ' lf la A m s t :
  Θ' = free Θ lf t ->
  mapsto Θ lf (eLam A m s t) ->
  Θ ;; eApp (eLab lf) (eLab la) => Θ' ;; m.[eLab la/]
| eval_unit Θ l :
  open Θ l ->
  Θ ;; eUnit => (l, eUnit) :: Θ ;; eLab l
| eval_it Θ l :
  open Θ l ->
  Θ ;; eIt => (l, eIt) :: Θ ;; eLab l
| eval_sigma Θ A B s r t l :
  open Θ l ->
  Θ ;; eSigma A B s r t => (l, eSigma A B s r t) :: Θ ;; eLab l
| eval_pairL Θ Θ' m m' n :
  Θ ;; m => Θ' ;; m' ->
  Θ ;; ePair m n => Θ' ;; ePair m' n
| eval_pairR Θ Θ' l n n' :
  Θ ;; n => Θ' ;; n' ->
  Θ ;; ePair (eLab l) n => Θ' ;; ePair (eLab l) n'
| eval_letin1 Θ Θ' m m' n :
  Θ ;; m => Θ' ;; m' ->
  Θ ;; eLetIn1 m n => Θ' ;; eLetIn1 m' n
| eval_iota1 Θ l n :
  mapsto Θ l eIt ->
  Θ ;; eLetIn1 (eLab l) n => Θ ;; n

where "Θ ;; m => Θ' ;; n" := (eval Θ m Θ' n).
