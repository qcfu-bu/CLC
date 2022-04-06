(* DIY QTT *)
Axiom semi_ring : U.
Axiom zero : semi_ring.
Axiom one  : semi_ring.
Axiom add : semi_ring -> semi_ring -> semi_ring.
Axiom mul : semi_ring -> semi_ring -> semi_ring.
Axiom lte : semi_ring -> semi_ring -> U.
(* and various axioms describing the behavior of the semi_ring *)

(* All definitions here should ideally be encapsulated as abstract types. *)
Inductive T (A : U) : A -> semi_ring -> L :=
| q : (x : A) -> (sr : semi_ring) -> T A x sr.

Definition split 
  (A : U) (x : A) (q1 q2 q3 : semi_ring) 
  (pf : eq semi_ring (add q1 q2) q3) 
  (t : T A x q3) 
: T A x q1 ^ T A x q2 := 
  match t in T A x q3 return
    T A x q1 ^ T A x q2
  with
  | q x _ => { q x q1, q x q2 }
  end.

Definition weaken 
  (A : U) (x : A) (q1 q2 : semi_ring) 
  (pf : lte q1 q2) 
  (t : T A x q2) 
: T A x q1 := 
  match t in T A x q2 return
    T A x q1
  with
  | q x _ => q x q1
  end.

Definition apply 
  (A : U)
  (B : A -> U)
  (f : (x : A) -> B x)
  (x : A) 
: T ((x : A) -> B x) f one -o T A x one -o T (B x) (f x) one := 
  fun t1 t2 => 
  match t1 in T _ f q return
    T A x one -o T (B x) (f x) one
  with
  | q f _ => fun t2 =>
    match t2 in T A x q return
      T (B x) (f x) one
    with
    | q x _ => q (f x) one
    end
  end t2.

Definition main : unit := ().
