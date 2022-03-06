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

Inductive value : term -> Prop :=
| value_sort s l : value (Sort s l)
| value_pi A B s t : value (Pi A B s t)
| value_lam A m s t : value (Lam A m s t)
| value_unit : value Unit
| value_it : value It
| value_sigma A B s r t : value (Sigma A B s r t)
| value_pair lm ln t : value (Pair (Ptr lm) (Ptr ln) t).

Inductive venv : env term -> Prop :=
| venv_nil : venv nil
| venv_cons Θ l v : venv Θ -> value v -> venv ((l, v) :: Θ).

Reserved Notation "Θ ;; m => Θ' ;; n" 
  (at level 80, m, Θ', n at next level).

Inductive eval : env term -> term -> env term -> term -> Prop :=
| eval_sort Θ s i l :
  open Θ l ->
  Θ ;; Sort s i => (l, Sort s i) :: Θ ;; Ptr l
| eval_pi Θ A B s t l :
  open Θ l ->
  Θ ;; Pi A B s t => (l, Pi A B s t) :: Θ ;; Ptr l
| eval_lam Θ A m s t l :
  open Θ l ->
  Θ ;; Lam A m s t => (l, Lam A m s t) :: Θ ;; Ptr l
| eval_appL Θ Θ' m m' n :
  Θ ;; m => Θ' ;; m' ->
  Θ ;; App m n => Θ' ;; App m' n
| eval_appR Θ Θ' l n n' :
  Θ ;; n => Θ' ;; n' ->
  Θ ;; App (Ptr l) n => Θ' ;; App (Ptr l) n'
| eval_beta Θ Θ' lf la A m s t :
  Θ' = free Θ lf t ->
  mapsto Θ lf (Lam A m s t) ->
  Θ ;; App (Ptr lf) (Ptr la) => Θ' ;; m.[Ptr la/]
| eval_unit Θ l :
  open Θ l ->
  Θ ;; Unit => (l, Unit) :: Θ ;; Ptr l
| eval_it Θ l :
  open Θ l ->
  Θ ;; It => (l, It) :: Θ ;; Ptr l
| eval_sigma Θ A B s r t l :
  open Θ l ->
  Θ ;; Sigma A B s r t => (l, Sigma A B s r t) :: Θ ;; Ptr l
| eval_pairL Θ Θ' m m' n t :
  Θ ;; m => Θ' ;; m' ->
  Θ ;; Pair m n t => Θ' ;; Pair m' n t
| eval_pairR Θ Θ' l n n' t :
  Θ ;; n => Θ' ;; n' ->
  Θ ;; Pair (Ptr l) n t => Θ' ;; Pair (Ptr l) n' t
| eval_pairV Θ l lm ln t :
  open Θ l ->
  Θ ;; Pair (Ptr lm) (Ptr ln) t => 
  (l, Pair (Ptr lm) (Ptr ln) t) :: Θ ;; Ptr l
| eval_letin1 Θ Θ' m m' n :
  Θ ;; m => Θ' ;; m' ->
  Θ ;; LetIn1 m n => Θ' ;; LetIn1 m' n
| eval_iota1 Θ l n :
  mapsto Θ l It ->
  Θ ;; LetIn1 (Ptr l) n => Θ ;; n
| eval_iota2 Θ Θ' lm ln l n t :
  Θ' = free Θ l t ->
  mapsto Θ l (Pair (Ptr lm) (Ptr ln) t) ->
  Θ ;; LetIn2 (Ptr l) n => Θ' ;; n.[Ptr ln,Ptr ln/]
where "Θ ;; m => Θ' ;; n" := (eval Θ m Θ' n).

Theorem progress m A Θ :
  nil ⊢ m : A -> 