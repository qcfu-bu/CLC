# Concurrent Calculus of Linear Constructions

## Core typing rules

```text
Γ ▹ U
----------------
Γ ⊢ s@i : U@i+1


Γ ▹ U    Γ ⊢ A : s@i    [Γ, x :s A] ⊢ B : r@i
----------------------------------------------
Γ ⊢ Πt (x :s A).B : t@i


Γ ▹ U
-----------------
Γ, x :s A ⊢ x : A


Γ ▹ t     [Γ] ⊢ Πt (x :s A).B : t@i     Γ, x :s A ⊢ n : B
----------------------------------------------------------
Γ ⊢ λt (x :s A).n : Πt (x :s A).B


Γ2 ▹ s    Γ1 ⊢ m : Πt (x :s A).B     Γ2 ⊢ n : A
------------------------------------------------
Γ1 + Γ2 ⊢ m n : B[n/x]


Γ ⊢ m : A     [Γ] ⊢ B : s@i     A ⪯ B
--------------------------------------
Γ ⊢ m : B
```

## Data typing rules

```text
Γ ▹ U     Γ ⊢ A : s@i     [Γ, x :s A] ⊢ B : r@i     s + r ≤ t
--------------------------------------------------------------
Γ ⊢ Σt (x :s A :r B)


Γ1 ▹ s     Γ2 ▹ r
[Γ1 + Γ2] ⊢ Σt (x :s A :r B) : t@i      Γ1 ⊢ m : A      Γ2 ⊢ n : B[m/x]
------------------------------------------------------------------------
Γ1 + Γ2 ⊢ ⟨m, n⟩ : Σt (x :s A :r B)


Γ1 ⊢ m : Σt (x :s A :r B)      
[Γ2, z :t Σt (x :s A :r B)] ⊢ C : q@i
Γ2, x :s A, y :r B ⊢ N : C[⟨x, y⟩/z]
----------------------------------------------------------
Γ1 + Γ2 ⊢ let ⟨x, y⟩ = m in n : C[m/z]
```

## Examples

### Enforcement of dynamic checks

```text
a0 : Ch(?(x : pkt).(if hashCheck x then ![true] else ![false]).end!)

let (n :U pkt, a1 :L Ch((if hashCheck n then ![true] else ![false]).end!)) = recv a0 in
match hashCheck n as r return
  (if r then ![true] else ![false]).end! -> unit
with
| true  => fun a2 => 
  let a3 = send a2 [true] in
  close a
| false => fun a2 => 
  let a3 = send a2 [false] in
  close a
end a1
```
