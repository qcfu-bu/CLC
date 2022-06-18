# Concurrent Calculus of Linear Constructions with Interpreted Duality

## Sort relations

### Order
```
≤  U  L
U  T  T
L  F  T
```

### Addition
```
⋅  U  L
U  U  L
L  L  L
```

## Core typing rules

```
Γ ▹ U
———————————
Γ ⊢ s :U U


Γ ▹ U    Γ ⊢ A :U s    [Γ, x :s A] ⊢ B :U r
———————————————————————————————————————————
Γ ⊢ Πt (x :s A :r B) :U t


Γ ▹ U
———————————————————
Γ, x :s A ⊢ x :s A


Γ ▹ t     [Γ] ⊢ Πt (x :s A :r B) :U t     Γ, x :s A ⊢ n :r B
————————————————————————————————————————————————————————————
Γ ⊢ λt (x :s A).n :t Πt (x :s A :r B)


Γ2 ▹ s    Γ1 ⊢ m :t Πt (x :s A :r B)     Γ2 ⊢ n :s A
—————————————————————————————————————————————————————
Γ1 ∘ Γ2 ⊢ m n :r B[n/x]


Γ ▹ U     Γ ⊢ A :U U     Γ, f :U A ⊢ m :U A
———————————————————————————————————————————
Γ ⊢ μ (f : A).m :U A


Γ ⊢ m :s A     [Γ] ⊢ B :U s     A ⪯ B
—————————————————————————————————————
Γ ⊢ m :s B
```

## Data typing rules

```
Γ ▹ U
—————————————
Γ ⊢ unit :U U


Γ ▹ U
———————————————
Γ ⊢ () :U unit


Γ1 ⊢ m :U unit     Γ2 ⊢ n :s A
———————————————————————————————
Γ1 ∘ Γ2 ⊢ let () = m in n :s A


Γ ▹ U
—————————————
Γ ⊢ bool :U U


Γ ▹ U
————————————————
Γ ⊢ true :U bool


Γ ▹ U
————————————————
Γ ⊢ false :U bool


Γ1 ▹ s     Γ1 ⊢ m :U bool     [Γ2, x :s bool] ⊢ A :U t
Γ2 ⊢ n1 :t A[true/x]     Γ2 ⊢ n2 :t A[false/x]
——————————————————————————————————————————————————————————
Γ1 ∘ Γ2 ⊢ if m then n1 else n2 :t A[m/x]


Γ ▹ U     Γ ⊢ A :U s     [Γ, x :s A] ⊢ B :U r     s ⋅ r ≤ t
———————————————————————————————————————————————————————————
Γ ⊢ Σt (x :s A :r B) :U t


Γ1 ▹ s     Γ2 ▹ r
[Γ1 ∘ Γ2] ⊢ Σt (x :s A :r B) :U t      Γ1 ⊢ m :s A      Γ2 ⊢ n :r B[m/x]
————————————————————————————————————————————————————————————————————————
Γ1 ∘ Γ2 ⊢ ⟨m, n⟩t :t Σt (x :s A :r B)


Γ1 ⊢ m :t Σt (x :s A :r B)     Γ1 ▹ k     t ≤ k
[Γ2, z :k Σt (x :s A :r B)] ⊢ C :U q
Γ2, x :s A, y :r B ⊢ n :q C[⟨x, y⟩t/z]
————————————————————————————————————————————————
Γ1 ∘ Γ2 ⊢ let ⟨x, y⟩ = m in n :q C[m/z]
```

## Session typing rules

```
Γ ▹ U
—————————————
Γ ⊢ main :U L


Γ ▹ U
——————————————
Γ ⊢ proto :U U


Γ ▹ U
——————————————————
Γ ⊢ end l :U proto


Γ ▹ U     Γ ⊢ A :U s     [Γ, x :s A] ⊢ B :U proto
—————————————————————————————————————————————————
Γ ⊢ l(x :s A).B :U proto


Γ ▹ U     Γ ⊢ A :U proto i
———————————————————————————
Γ ⊢ ch l A :U L


[Γ1] ⊢ A :U proto    l1 = ¬l2
Γ1 ⊢ m :L main     Γ2 ⊢ n :t Πt (x :L ch l2 A :s C)
———————————————————————————————————————————————————
Γ1 ∘ Γ2 ⊢ fork m n :L ΣL (x :L ch l1 A :L main)


Γ ⊢ m :L ch l1 (l2(x :s A).B)    xor l1 l2 = true
—————————————————————————————————————————————————
Γ ⊢ send m :L ΠL (x :s A :L ch B)


Γ ⊢ m :L ch l1 (l2(x :s A).B)    xor l1 l2 = false
——————————————————————————————————————————————————
Γ ⊢ recv m :L ΣL (x :s A :L ch B)


Γ ⊢ m :L ch l1 (end l2)    xor l1 l2 = true
———————————————————————————————————————————
Γ ⊢ close m :U unit


Γ ⊢ m :L ch l1 (end l2)    xor l2 l2 = false
————————————————————————————————————————————
Γ ⊢ wait m :U unit
```
