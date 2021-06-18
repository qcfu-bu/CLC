Require Import Program.

Inductive SN (N : nat) : Type :=
| sn : forall (n : nat), SN n.

Inductive Sigma (A : Prop) (F : A -> Prop) : Prop :=
| pair : forall (x : A), F x -> Sigma A F.

Definition fst A F (p : Sigma A F) : A := 
  match p with
  | pair _ _ x _ => x
  end.

Definition snd A F (p : Sigma A F) : (F (fst A F p)) := 
  match p with
  | pair _ _ _ y => y
  end.

Print True.

Inductive PNat : Prop :=
| PO : PNat
| PS : PNat -> PNat.

Definition repack (p : Sigma True (fun _ => True)) : True :=
  match p with
  | pair _ _ x y => snd _ _ (pair PNat (fun _ => True) PO I)
  end.

Print repack.

Inductive List (A : Type) : Type :=
| Nil : List A
| Cons : A -> List A -> List A.

Definition ls : List nat := 
  Cons nat O (Cons nat O (Nil nat)).
