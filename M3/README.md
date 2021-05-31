# M3

## Notes

### Functional fragment of QTT. 

* Terms are partially annotated. 
* Typechecking is bi-directional.
* Bindlib representation of variables
* LetIn construct

### Rig

* 0: static
* 1: linear
* ω: intuitionistic

#### Add
```
ρ+0 = 0+ρ = ρ
1+1 = ω
ρ+ω = ω+ρ = ω
```

#### Times
```
ρ*0 = 0*ρ = 0
ρ*1 = 1*ρ = ρ
ω*ω = ω
```

#### Order
0 ≰ 1 gives rise to linearity.
```
0 ≤ 0, 0 ≤ &, 0 ≤ ω
1 ≤ 1, 1 ≤ &, 1 ≤ ω 
& ≤ &, & ≤ ω
ω ≤ ω
```


### Typechecking algorithm
Bi-directional typechecking through context inference.

```
Γ ↓ Δ ⊢ ρ a ↓ A               Γ ↓ Δ ⊢ ρ a ↑ A
----------------(↓↑)          ----------------------(↑↓)
Γ ↓ Δ ⊢ ρ a ↑ A               Γ ↓ Δ ⊢ ρ (a :: A) ↓ A
```

```
-----------------------------------------(id)
Γ, 0 x : A, Γ' ↓ Γ, ρ x : A, Γ' ⊢ ρ x ↓ A
```

```
-------------(*)
Γ ↓ Γ ⊢ 0 * ↓ *
```

```
Γ ↓ Δ ⊢ 0 A ↑ *     Γ, 0 x : A ↓ Δ, 0 x : A ⊢ 0 B ↑ *
-----------------------------------------------------(π)
Γ ↓ Δ ⊢ 0 (π x : A) → B ↓ *
```

```
Γ, 0 x : A ↓ Δ, π' x : A ⊢ 1 b ↑ B     π' ≤ π
---------------------------------------------(→I)
Γ ↓ ρ*Δ ⊢ ρ λx. b ↑ (π x : A) → B
```

```
Γ ↓ Δ ⊢ ρ f ↓ (π x : A) → B     Γ ↓ Δ' ⊢ ρ*π a ↑ A
--------------------------------------------------(→E)
Γ ↓ Δ + Δ' ⊢ ρ (f a) ↓ B[a/x]
```


## References
* https://gist.github.com/gabriel-barrett/0de85a606b64886052854422fb05ce0c
* https://gist.github.com/gabriel-barrett/11988a272bc52f0e848db6eceb03417a
* https://richarde.dev/papers/2020/quantitative/quantitative.pdf
* https://www.type-driven.org.uk/edwinb/papers/idris2.pdf
* https://bentnib.org/quantitative-type-theory.pdf
* https://link.springer.com/chapter/10.1007/978-3-319-30936-1_12