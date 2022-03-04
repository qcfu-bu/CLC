From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sort : Type := U | L.

Definition elem T := option (T * sort).
Definition context T := seq (elem T).


Notation "m :U Γ" := (Some (m, U) :: Γ) (at level 30).
Notation "m :L Γ" := (Some (m, L) :: Γ) (at level 30).
Notation "m :{ s } Γ" := (Some (m, s) :: Γ) (at level 30).
Notation "_: Γ" := (None :: Γ) (at level 30).

Reserved Notation "Γ1 + Γ2 => Γ" (at level 40).
Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  nil + nil => nil
| merge_left Γ1 Γ2 Γ m : 
  Γ1 + Γ2 => Γ ->
  m :U Γ1 + m :U Γ2 => m :U Γ
| merge_right1 Γ1 Γ2 Γ m :
  Γ1 + Γ2 => Γ ->
  m :L Γ1 + _: Γ2 => m :L Γ
| merge_right2 Γ1 Γ2 Γ m :
  Γ1 + Γ2 => Γ ->
  _: Γ1 + m :L Γ2 => m :L Γ
| merge_null Γ1 Γ2 Γ :
  Γ1 + Γ2 => Γ ->
  _: Γ1 + _: Γ2 => _: Γ
where "Γ1 + Γ2 => Γ" := (merge Γ1 Γ2 Γ).

Reserved Notation "Γ |> s" (at level 40).
Inductive key T : context T -> sort -> Prop :=
| key_nil s :
  nil |> s
| key_u Γ m :
  Γ |> U ->
  m :U Γ |> U
| key_l Γ m s :
  Γ |> L ->
  m :{s} Γ |> L
| key_n Γ s :
  Γ |> s ->
  _: Γ |> s
where "Γ |> s" := (key Γ s).

Inductive has {T} `{Ids T} `{Subst T} :
  context T -> var -> sort -> T -> Prop :=
| has_O Γ A s :
  Γ |> U ->
  has (A :{s} Γ) 0 s A.[ren (+1)]
| has_S Γ A B x s :    
  has Γ x s A ->
  has (B :U Γ) x.+1 s A.[ren (+1)]
| has_N Γ A x s :
  has Γ x s A ->
  has (_: Γ) x.+1 s A.[ren (+1)].

Fixpoint re T (Γ : context T) : context T :=
  match Γ with
  | Some (m, U) :: Γ => Some (m, U) :: re Γ
  | _ :: Γ => None :: re Γ
  | _ => nil
  end.
Notation "[ Γ ]" := (re Γ).

Lemma merge_sym T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ -> Γ2 + Γ1 => Γ.
Proof.
  elim; move=>*; eauto using merge.
Qed.

Lemma merge_pure T (Γ : context T) :
  Γ |> U -> Γ + Γ => Γ.
Proof.
  move e:(U)=> s k.
  elim: k e; move=>//=*; eauto using merge.
Qed.

Lemma merge_reL T (Γ : context T) :
  [Γ] + Γ => Γ.
Proof.
  elim: Γ; eauto using merge.
  move=> [[A[|]]|] Γ mrg//=; eauto using merge.
Qed.

Lemma merge_reR T (Γ : context T) :
  Γ + [Γ] => Γ.
Proof.
  elim: Γ; eauto using merge.
  move=> [[A[|]]|] Γ mrg//=; eauto using merge.
Qed.

Lemma merge_pure_inv T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ -> Γ |> U -> Γ1 |> U /\ Γ2 |> U.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
    firstorder; eauto using key.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
  move=> Γ1 Γ2 Γ mrg1 ih mrg2.
    inv mrg2.
    firstorder; eauto using key.
Qed.

Lemma merge_pureL T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ -> Γ1 |> U -> Γ = Γ2.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
    by rewrite ih.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
  move=> Γ1 Γ2 Γ A mrg1 ih mrg2.
    inv mrg2.
    by rewrite ih.
  move=> Γ1 Γ2 Γ mrg1 ih mrg2.
    inv mrg2.
    by rewrite ih.
Qed.

Lemma merge_pure_pure T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ -> Γ1 |> U -> Γ2 |> U -> Γ |> U.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg ih k1 k2.
    inv k1. inv k2.
    by eauto using key.
  move=> Γ1 Γ2 Γ A mrg ih k.
    by inv k.
  move=> Γ1 Γ2 Γ A mrg ih _ k.
    by inv k.
  move=> Γ1 Γ2 Γ mrg ih k1 k2.
    inv k1. inv k2.
    by eauto using key.
Qed.

Lemma merge_pure_eq T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ -> Γ1 |> U -> Γ2 |> U -> Γ1 = Γ2.
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg ih k1 k2.
    inv k1. inv k2.
    by rewrite ih.
  move=> Γ1 Γ2 Γ A _ _ k.
    inv k.
  move=> Γ1 Γ2 Γ A _ _ _ k.
    inv k.
  move=> Γ1 Γ2 Γ mrg ih k1 k2.
    inv k1. inv k2.
    by rewrite ih.
Qed.

Lemma merge_re_re T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ -> [Γ1] = [Γ2] /\ [Γ1] = [Γ] /\ [Γ2] = [Γ].
Proof.
  elim=>//={Γ1 Γ2 Γ}.
  move=> Γ1 Γ2 Γ A mrg[->[->_]]//.
  move=> Γ1 Γ2 Γ A mrg[->[->_]]//.
  move=> Γ1 Γ2 Γ A mrg[->[->_]]//.
  move=> Γ1 Γ2 Γ mrg[->[->_]]//.
Qed.

Lemma merge_re_id T (Γ : context T) :
  [Γ] + [Γ] => [Γ].
Proof.
  elim: Γ; eauto using merge.
  move=> [[A[|]]|] Γ mrg; eauto using merge.
Qed.

Lemma re_invo T (Γ : context T) : [Γ] = [[Γ]].
Proof.
  elim: Γ=>//.
  move=> [[A[|]]|] Γ//=<-//.
Qed.

Lemma pure_re T (Γ : context T) : Γ |> U -> Γ = [Γ].
Proof.
  elim: Γ=>//.
  move=> [[A[|]]|] Γ ih k//=.
  inv k. by rewrite<-ih.
  inv k.   
  inv k. by rewrite<-ih.
Qed.

Lemma re_pure T (Γ : context T) : [Γ] |> U.
Proof.
  elim: Γ; eauto using key.
  move=> [[A[|]]|] Γ k//=; eauto using key.
Qed.

Lemma hasU_re {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  has Γ x U A -> has [Γ] x U A.
Proof.
  move e:(U) => s h.
  elim: h e=>{Γ x s A}.
  move=> Γ A s k <-//=.
    constructor.
    by rewrite<-pure_re.
  move=> Γ A B x s h ih e//=; subst.
    by constructor; eauto.
  move=> Γ A x s h ih e//=; subst.
    by constructor; eauto.
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  ~has [Γ] x L A.
Proof.
  elim: Γ x A.
  move=>//=x A h. inv h.
  move=>[[B[|]]|] Γ ih x A //=h.
  inv h. apply: ih; eauto.
  inv h. apply: ih; eauto.
  inv h. apply: ih; eauto.
Qed.

Lemma hasU_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  has Γ x U A -> Γ |> U.
Proof.
  move e:(U)=>s h.
  elim: h e=>{Γ x A s}.
  move=> Γ A s ih <-; eauto using key.
  move=> Γ A B x s h ih e; subst; eauto using key.
  move=> Γ A x s h ih e; subst; eauto using key.
Qed.

Lemma hasL_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  has Γ x L A -> ~ Γ |> U.
Proof.
  move e:(L)=>s h.
  elim: h e=>{Γ x A s}.
  move=> Γ A s k e contra; subst. inv contra.
  move=> Γ A B x s h ih e contra. 
    inv contra.
    by apply: ih.
  move=> Γ A x s h ih e contra.
    inv contra.
    by apply ih.
Qed.

Lemma has_inj {T} `{Ids T} `{Subst T} (Γ : context T) x s t A B :
  has Γ x s A -> has Γ x t B -> A = B /\ s = t.
Proof.
  move=> h.
  elim: h B t=>{Γ x s A}.
  move=> Γ A s k B t h.
    by inv h.
  move=> Γ A B x s hA ih B0 t hB.
    inv hB.
    by move:(ih _ _ H6)=>[->->]//.
  move=> Γ A x s hA ih B0 t hB.
    inv hB.
    by move:(ih _ _ H3)=>[->->]//.
Qed.

Lemma merge_splitL T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ ->
  forall Δ1 Δ2,
    Δ1 + Δ2 => Γ1 ->
    exists Δ, 
      Δ1 + Γ2 => Δ /\ Δ + Δ2 => Γ.
Proof.
  elim=>{Γ1 Γ2 Γ}.
  move=> Δ1 Δ2 mrg. 
    inv mrg.
    exists nil.
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :U G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
Qed.

Lemma merge_splitR T (Γ1 Γ2 Γ : context T) :
  Γ1 + Γ2 => Γ ->
  forall Δ1 Δ2,
    Δ1 + Δ2 => Γ1 ->
    exists Δ,
      Δ2 + Γ2 => Δ /\ Δ1 + Δ => Γ.
Proof.
  elim=>{Γ1 Γ2 Γ}.
  move=> Δ1 Δ2 mrg. 
    inv mrg.
    exists nil.
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :U G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ A mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (A :L G).
    by eauto using merge.
  move=> Γ1 Γ2 Γ mrg ih Δ1 Δ2 mrg1.
    inv mrg1.
    move:(ih _ _ H2)=>[G[mrg2 mrg3]].
    exists (_: G).
    by eauto using merge.
Qed.
