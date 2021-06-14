# M6

## Influences
* LLF
  - context merge
  - purity assertion for types
* QTT
  - context management via rig labeling
  - 0 binding
* LNLD
  - sort separation between modalities
  - Linear has sort Type
* L3
  - linear capabilities
  - computational irrelevance of capabilities
* ATS
  - implicit modality conversions via sorts
  - arrow modalities

## Typing Rules

### Rig

* 0: static
* 1: linear
* ω: intuitionistic

```
ρ+0 = 0+ρ = ρ
1+1 = ω
ρ+ω = ω+ρ = ω

ρ*0 = 0*ρ = 0
ρ*1 = 1*ρ = ρ
ω*ω = ω

0 ≤ 0, 0 ≤ &, 0 ≤ ω
1 ≤ 1, 1 ≤ &, 1 ≤ ω 
& ≤ &, & ≤ ω
ω ≤ ω
```

### Axioms
```
                                        Γ ⊢ X : Uᵢʳ
----------------   -----------------   -------------------
∅ ⊢ Uᵢʷ : Uᵢ₊₁ʷ     ∅ ⊢ Uᵢ¹ : Uᵢ₊₁ʷ     [x:X¹::r] ⊢ x : X


Γ₁ ⊢ a : B    Γ₂ ⊢ A : Uᵢʳ
--------------------------
Γ₁,[x:A⁰::r] ⊢ a : B
```

### Type Formation
```
Γ̅₁ ⊢ X : Uᵢᵃ   Γ̅₂,[x:Xʳ::a] ⊢ Y : Uᵢᵇ
-------------------------------------
Γ̅₁ + Γ̅₂ ⊢ (x:Xᵃ) -> Y : Uᵢʷ


Γ̅₁ ⊢ X : Uᵢᵃ   Γ̅₂,[x:Xʳ::a] ⊢ Y : Uᵢᵇ
-------------------------------------
Γ̅₁ + Γ̅₂ ⊢ (x:Xᵃ) >> Y : Uᵢ¹


Γ̅₁ ⊢ A : Uᵢᵃ   Γ̅₂,[x:Aʳ::a] ⊢ B : Uᵢᵇ
-----------------------------------------
Γ̅₁ + Γ̅₂ ⊢ Σx:X.Y : Uᵢᶜ    (c = min(a, b))


Γ̅₁ ⊢ X : Uᵢʷ   Γ̅₂ ⊢ e : X    Γ̅₃ ⊢ e' : X
-----------------------------------------
Γ̅₁ + Γ̅₂ + Γ̅₃ ⊢ e ≡ₓ e' : Uᵢʷ
```

### Term Formation
```
Γ̅₁ ⊢ (x:Xᵃ) -> Y : Uᵢʷ    Γ₂,[x:Xʳ::a] ⊢ e : Y    r ≤ a
-------------------------------------------------------
Γ₂ ⊢ λx.e : (x:Xᵃ) -> Y


Γ̅₁ ⊢ (x:Xᵃ) >> Y : Uᵢ¹    Γ₂,[x:Xʳ::a] ⊢ e : Y    r ≤ a
-------------------------------------------------------
Γ₂ ⊢ λ̂x.e : (x:Xᵃ) >> Y


Γ₁ ⊢ e : (x:Xᵃ) -> Y    Γ₂ ⊢ e' : X
------------------------------------
Γ₁ + aΓ₂ ⊢ e e' : [e'/x]Y


Γ₁ ⊢ e : (x:Xᵃ) >> Y    Γ₂ ⊢ e' : X
------------------------------------
Γ₁ + aΓ₂ ⊢ e e' : [e'/x]Y


Γ̅₁ ⊢ Σx:Xᵃ.Yᵇ : Uᵢᶜ    Γ₂ ⊢ e : X    Γ₃ ⊢ e' : [e/x]Y
------------------------------------------------------
Γ₂ + Γ₃ ⊢ (e, e') : Σx:Xᵃ.Yᵇ


Γ̅₁ ⊢ e : Σx:Xᵃ.Yᵇ   Γ₂,[x:Xʳ::a],[y:Yˢ::b] ⊢ e' : Z   r ≤ a ∧ s ≤ b
-------------------------------------------------------------------
Γ₁ + Γ₂ ⊢ let (x, y) = e in e' : let (x, y) = e in Z


Γ̅₁ ⊢ X : Uᵢʷ    Γ₂ ⊢ x : X
---------------------------
Γ₂ ⊢ reflₓ x : x ≡ₓ x


Γ₁ ⊢ X : Uᵢᵃ    Γ₂ ⊢ e : X     Γ₃,[x:Xʳ::a] ⊢ e' : Y    r ≤ a
-------------------------------------------------------------
Γ₂ + Γ₃ ⊢ let x = e in e' : [e/x]Y
```

## Notes
The type system is fairly pleasant for programming, but the requirement
of inferring universes makes type checking inefficient.

The let-binding rule is deceptively difficult. A proper formalization will
likely have several let binding rules to resolve different use cases.

## References
* https://dl.acm.org/doi/10.5555/788018.788831
* https://link.springer.com/chapter/10.1007/3-540-58027-1_24
* https://link.springer.com/chapter/10.1007/3-540-52335-9_47
* https://link.springer.com/article/10.1007/BF01211308
* https://homotopytypetheory.org/book/
* https://www.cs.cmu.edu/~fp/courses/15816-f01/handouts/linfp.pdf
* https://dl.acm.org/doi/10.1145/2775051.2676969
* https://gist.github.com/gabriel-barrett/0de85a606b64886052854422fb05ce0c
* https://gist.github.com/gabriel-barrett/11988a272bc52f0e848db6eceb03417a
* https://richarde.dev/papers/2020/quantitative/quantitative.pdf
* https://www.type-driven.org.uk/edwinb/papers/idris2.pdf
* https://bentnib.org/quantitative-type-theory.pdf
* https://link.springer.com/chapter/10.1007/978-3-319-30936-1_12