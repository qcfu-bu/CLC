From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8.
Require Export cclc_eval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive proc :=
| Exp (m : term)
| Par (p q : proc)
| Nu (p : proc).

Notation "⟨ e ⟩" := (Exp e).
Notation "p ∣ q" := (Par p q) (at level 20).
Notation "ν." := (Nu) (at level 20).

Declare Scope proc_scope.
Delimit Scope proc_scope with P.
Bind Scope proc_scope with proc.
Local Open Scope proc_scope.

Fixpoint proc_subst (p : proc) (σ : var -> term) : proc :=
  match p with
  | ⟨m⟩ => Exp (m.[σ])
  | p ∣ q => Par (proc_subst p σ) (proc_subst q σ)
  | ν.p => Nu (proc_subst p (upn 2 σ))
  end.

Arguments proc_subst : simpl nomatch.

Notation "p .[ σ ]" := (proc_subst p σ) 
  (at level 2, σ at level 200, left associativity,
    format "p .[ σ ]") : proc_scope.
Notation "p .[ m /]" := (proc_subst p (m .: ids)) 
  (at level 2, m at level 200, left associativity,
    format "p .[ m /]") : proc_scope.
Notation "p .[ m1 , m2 , .. , mn /]" := 
  (proc_subst p (scons m1 (scons m2 .. (scons mn ids) ..)))
  (at level 2, left associativity,
    format "p '[ ' .[ m1 , '/' m2 , '/' .. , '/' mn /] ']'") : proc_scope.

Inductive congr0 : proc -> proc -> Prop :=
| congr0_par_sym p q :
  congr0 (p ∣ q) (q ∣ p)
| congr0_assoc o p q :
  congr0 (o ∣ (p ∣ q)) ((o ∣ p) ∣ q)
| congr0_associ o p q :
  congr0 ((o ∣ p) ∣ q) (o ∣ (p ∣ q)) 
| congr0_scope p (q : proc) :
  congr0 ((ν.p) ∣ q) (ν.(p ∣ q.[ren (+2)]))
| congr0_scopei p (q : proc) :
  congr0 (ν.(p ∣ q.[ren (+2)])) ((ν.p) ∣ q) 
| congr0_par p p' q q' :
  congr0 p p' ->
  congr0 q q' ->
  congr0 (p ∣ q) (p' ∣ q')
| congr0_pari p p' q q' :
  congr0 p p' ->
  congr0 q q' ->
  congr0 (p' ∣ q') (p ∣ q) 
| congr0_nu p p' :
  congr0 p p' ->
  congr0 (ν.p) (ν.p')
| congr0_nui p p' :
  congr0 p p' ->
  congr0 (ν.p') (ν.p).
Notation "p ≡ q" := (conv congr0 p q) (at level 30).

Reserved Notation "p --> q" (at level 30).
Inductive proc_step : proc -> proc -> Prop :=
| proc_fork c c' m m' :
  c' = eren c (+2) ->
  m' = m.[ren (+2)]%subst ->
  ⟨c.[Fork (Var 0) m]⟩ -->
  ν.(⟨c'.[Pair (Var 0) (Var 2) L]⟩ ∣ ⟨App m' (Var 1)⟩)
| proc_com c d v :
  ν.(⟨c.[App (Send (Var 0)) v]⟩ ∣ ⟨d.[Recv (Var 1)]⟩) -->
  ν.(⟨c.[Var 0]⟩ ∣ ⟨d.[Pair v (Var 1) L]⟩)
| proc_comi c d v :
  ν.(⟨c.[App (Send (Var 1)) v]⟩ ∣ ⟨d.[Recv (Var 0)]⟩) -->
  ν.(⟨c.[Var 1]⟩ ∣ ⟨d.[Pair v (Var 0) L]⟩)
| proc_end c c' d d' :
  c' = eren c (+2) ->
  d' = eren d (+2) ->
  ν.(⟨c'.[Close (Var 0)]⟩ ∣ ⟨d'.[Wait (Var 1)]⟩) -->
  ⟨c.[It]⟩ ∣ ⟨d.[It]⟩
| proc_endi c c' d d' :
  c' = eren c (+2) ->
  d' = eren d (+2) ->
  ν.(⟨c'.[Close (Var 1)]⟩ ∣ ⟨d'.[Wait (Var 0)]⟩) -->
  ⟨c.[It]⟩ ∣ ⟨d.[It]⟩
| proc_exp m n :
  m ~> n -> 
  ⟨m⟩ --> ⟨n⟩
| proc_par o p q :
  p --> q ->
  o ∣ p --> o ∣ q
| proc_nu p q :
  p --> q ->
  ν.p --> ν.q
| proc_congr p p' q q'  :
  p ≡ p' ->
  p' --> q' ->
  q' ≡ q ->
  p --> q
where "p --> q" := (proc_step p q)%C.

Lemma proc_subst_comp p σ1 σ2 : p.[σ1].[σ2] = p.[σ1 >> σ2].
Proof.
  elim: p σ1 σ2.
  move=>m σ1 σ2; asimpl; eauto.
  move=>p ihp q ihq σ1 σ2; asimpl.
    rewrite ihp.
    by rewrite ihq.
  move=>p ih σ1 σ2; asimpl.
    rewrite ih.
    by asimpl.
Qed.

Lemma proc_ids p : p.[ids] = p.
Proof.
  elim: p; asimpl=>//.
  move=>p->q->//.
  move=>p->//.
Qed.
